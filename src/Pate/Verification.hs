{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Verification
  ( verifyPairs
  ) where

import qualified Control.Concurrent.MVar as MVar
import           Control.Monad ( unless )
import qualified Control.Monad.Except as CME
import           Control.Monad.IO.Class ( liftIO )
import qualified Control.Monad.IO.Unlift as IO
import           System.IO as IO
import qualified Control.Monad.Trans as CMT
import qualified Data.ElfEdit as DEE
import qualified Data.Map as M
import qualified Data.Parameterized.SetF as SetF
import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.IORef as IO
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Time as TM
import qualified Data.Traversable as DT
import           GHC.Stack ( HasCallStack, callStack )
import qualified Lumberjack as LJ
import           Prelude hiding ( fail )
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Interface as W4

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Pate.Address as PAd
import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Discovery as PD
import qualified Pate.Discovery.ParsedFunctions as PD
import           Pate.Equivalence as PEq
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Event as PE
import qualified Pate.Hints as PH
import qualified Pate.Loader.ELF as PLE
import qualified Pate.Location as PL
import qualified Pate.Memory as PM
import qualified Pate.Memory.MemTrace as MT
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Solver as PS
import qualified Pate.SymbolTable as PSym
import qualified Pate.Verification.Override as PVO
import qualified Pate.Verification.Override.Library as PVOL
import qualified Pate.Verification.StrongestPosts as PSP
import           Pate.TraceTree

-- | Run code discovery using macaw
--
-- We run discovery in parallel, since we need to run it two to four times.
--
-- If we have hints for a binary (original or patched), we run discovery twice:
-- with and without hints. We then compare the two and report any discrepancies
-- that indicate that the hints could be wrong.
--
-- We report any errors in the hints:
--
-- * Hints that point to non-code data (bad)
--
-- * Hints not appearing in our discovery (good)
--
-- We use the hinted results (if any)
runDiscovery
  :: (PA.ValidArch arch)
  => LJ.LogAction IO (PE.Event arch)
  -> Maybe FilePath
  -- ^ Directory to save macaw CFGs to
  -> PA.SomeValidArch arch
  -> PH.Hinted (PLE.LoadedELF arch)
  -> PH.Hinted (PLE.LoadedELF arch)
  -> PC.PatchData
  -> CME.ExceptT PEE.EquivalenceError IO (PPa.PatchPair (PMC.BinaryContext arch))
runDiscovery logAction mCFGDir (PA.SomeValidArch archData) elf elf' pd = do
  binCtxO <- discoverCheckingHints PBi.OriginalRepr (PA.validArchOrigExtraSymbols archData) elf
  binCtxP <- discoverCheckingHints PBi.PatchedRepr (PA.validArchPatchedExtraSymbols archData) elf'
  liftIO $ LJ.writeLog logAction (PE.LoadedBinaries (PH.hinted elf) (PH.hinted elf'))
  return $ PPa.PatchPair binCtxO binCtxP
  where
    discover mdir repr extra e h = PD.runDiscovery archData mdir repr extra e h pd

    discoverCheckingHints repr extra e = do
      if | PH.hints e == mempty -> do
             (_, oCtxUnhinted) <- discover mCFGDir repr extra (PH.hinted e) mempty
             return oCtxUnhinted
         | otherwise -> do
             (hintErrors, oCtxHinted) <- discover mCFGDir repr extra (PH.hinted e) (PH.hints e)
             unless (null hintErrors) $ do
               let invalidSet = S.fromList hintErrors
               let invalidEntries = [ (name, addr)
                                    | (name, fd) <- PH.functionEntries (PH.hints e)
                                    , let addr = PH.functionAddress fd
                                    , S.member addr invalidSet
                                    ]
               liftIO $ LJ.writeLog logAction (PE.FunctionEntryInvalidHints repr invalidEntries)
             return oCtxHinted

verifyPairs ::
  forall arch.
  PA.ValidArch arch =>
  PA.SomeValidArch arch ->
  LJ.LogAction IO (PE.Event arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PC.VerificationConfig PA.ValidRepr ->
  PC.PatchData ->
  CME.ExceptT PEE.EquivalenceError IO (PEq.EquivalenceStatus)
verifyPairs validArch logAction elf elf' vcfg pd = do
  Some gen <- liftIO N.newIONonceGenerator
  sym <- liftIO $ WE.newExprBuilder WE.FloatRealRepr WE.EmptyExprBuilderState gen 

  -- NB, hash-consing is not strictly necessary, but I conjecture that it may be
  -- helpful for the kinds of problems we are facing.
  liftIO $ WE.startCaching sym

  doVerifyPairs validArch logAction elf elf' vcfg pd gen sym


findFunctionByName ::
  PBi.KnownBinary bin =>
  MM.ArchConstraints arch =>
  String ->
  PMC.BinaryContext arch bin ->
  IO (Maybe (PB.FunctionEntry arch bin))
findFunctionByName nm context = do
  let pfm = PMC.parsedFunctionMap context
  PD.findFunctionByName nm pfm
  
-- | Verify equality of the given binaries.
doVerifyPairs ::
  forall arch sym scope st fs.
  ( PA.ValidArch arch
  , sym ~ WE.ExprBuilder scope st fs
  , CB.IsSymInterface sym
  ) =>
  PA.SomeValidArch arch ->
  LJ.LogAction IO (PE.Event arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PH.Hinted (PLE.LoadedELF arch) ->
  PC.VerificationConfig PA.ValidRepr ->
  PC.PatchData ->
  N.NonceGenerator IO scope ->
  sym ->
  CME.ExceptT PEE.EquivalenceError IO PEq.EquivalenceStatus
doVerifyPairs validArch logAction elf elf' vcfg pd gen sym = do
  startTime <- liftIO TM.getCurrentTime
  (traceVals, llvmVals) <- case ( MS.genArchVals (Proxy @MT.MemTraceK) (Proxy @arch) Nothing
                                , MS.genArchVals (Proxy @MS.LLVMMemory) (Proxy @arch) Nothing) of
    (Just vs1, Just vs2) -> pure (vs1, vs2)
    _ -> CME.throwError $ PEE.loaderError $ PEE.UnsupportedArchitecture (DEE.headerMachine $ PLE.loadedHeader $ PH.hinted elf)
  ha <- liftIO CFH.newHandleAllocator
  contexts <- runDiscovery logAction (PC.cfgMacawDir vcfg) validArch elf elf' pd
  
  -- Implicit parameters for the LLVM memory model
  let ?memOpts = CLM.laxPointerMemOptions

  eval <- CMT.lift (MS.withArchEval traceVals sym pure)
  mvar <- CMT.lift (MT.mkMemTraceVar @arch ha)
  bvar <- CMT.lift (CC.freshGlobalVar ha (T.pack "block_end") W4.knownRepr)
  (undefops, ptrAsserts) <- liftIO $ MT.mkAnnotatedPtrOps sym

  -- PC values are assumed to be absolute
  pcRegion <- liftIO $ W4.natLit sym 0

  -- we arbitrarily assign disjoint regions for each area of memory
  globalRegion <- liftIO $ W4.natLit sym 0
  stackRegion <- liftIO $ W4.natLit sym 1

  startedAt <- liftIO TM.getCurrentTime
  topNonce <- liftIO $ (PF.ProofNonce <$> N.freshNonce gen)

  -- NOTE: This is using the global nonce generator because it gets sunk down
  -- into contexts where the scope type parameter is quantified out in ways that
  -- are not practical to recover without major refactoring.  This is just as
  -- safe but makes things significantly easier.
  symNonce <- liftIO (N.freshNonce N.globalNonceGenerator)
  ePairCache <- liftIO $ freshBlockCache
  statsVar <- liftIO $ MVar.newMVar mempty


  -- compute function entry pairs from the input PatchData
  upData <- unpackPatchData contexts pd
  -- include the process entry point, if configured to do so
  
  entryPoints' <- DT.forM (PC.cfgStartSymbols vcfg) $ \s -> do
    PPa.runPatchPairT $ PPa.forBins $ \bin -> do
      ctx <- PPa.get bin contexts
      (liftIO $ findFunctionByName s ctx) >>= \case
        Just start -> return start
        Nothing -> CME.throwError $ PEE.loaderError (PEE.ConfigError ("Missing Entry Point: " ++ s))
  
  topEntryPoint <- PPa.runPatchPairT $ PPa.forBins $ \bin -> do
    ctx <- PPa.get bin contexts
    liftIO $ PD.resolveFunctionEntry (PMC.binEntry ctx) (PMC.parsedFunctionMap ctx)
  let entryPoints = (topEntryPoint : entryPoints')

  PA.SomeValidArch archData <- return validArch
  let defaultInit = PA.validArchInitAbs archData

  -- inject an override for the initial abstract state
  contexts1 <- PPa.runPatchPairT $ PPa.forBins $ \bin -> do  
    context' <- PPa.get bin contexts
    let
      pfm = PMC.parsedFunctionMap context'
      mem = MBL.memoryImage (PMC.binary context')
    
    CME.foldM (\ctx entryPoint -> do
      blk <- PPa.get bin entryPoint
      let initAbs = PB.mkInitAbs defaultInit mem (PB.functionSegAddr blk)
      let ov = M.singleton (PB.functionSegAddr blk) initAbs
      pfm' <- liftIO $ PD.addOverrides PB.defaultMkInitialAbsState pfm ov
      return $ ctx { PMC.parsedFunctionMap = pfm' }) context' entryPoints
    
  let pPairs' = entryPoints ++ (unpackedPairs upData)
  let solver = PC.cfgSolver vcfg
  let saveInteraction = PC.cfgSolverInteractionFile vcfg
  let
    -- TODO, something real here
    syscallModel = MT.MacawSyscallModel ()

    exts = MT.macawTraceExtensions eval syscallModel mvar (trivialGlobalMap @_ @arch globalRegion) undefops

  
  (treeBuilder :: TreeBuilder '(sym, arch)) <- liftIO $ startSomeTreeBuilder (PA.ValidRepr sym validArch) (PC.cfgTraceTree vcfg)

  satCache <- liftIO $ IO.newIORef SetF.empty
  unsatCache <- liftIO $ IO.newIORef SetF.empty

  let targetRegsRaw = PC.cfgTargetEquivRegs vcfg

  targetRegs <- fmap S.fromList $ mapM (\r_raw -> case PA.readRegister @arch r_raw of
           Just r -> return r
           Nothing -> CME.throwError $ PEE.loaderError $ PEE.ConfigError $ "Unknown register: " ++ r_raw) targetRegsRaw
  
  liftIO $ PS.withOnlineSolver solver saveInteraction sym $ \bak -> do
    let ctxt = PMC.EquivalenceContext
          { PMC.handles = ha
          , PMC.binCtxs = contexts1
          , PMC.stackRegion = stackRegion
          , PMC.globalRegion = globalRegion
          , PMC._currentFunc = error "No function under analysis at startup"
          , PMC.originalIgnorePtrs = unpackedOrigIgnore upData
          , PMC.patchedIgnorePtrs = unpackedPatchIgnore upData
          , PMC.equatedFunctions = unpackedEquatedFuncs upData
          , PMC.observableMemory = unpackedObservableMemory upData
          }
        env = EquivEnv
          { envWhichBinary = Nothing
          , envValidArch = validArch
          , envCtx = ctxt
          , envArchVals = traceVals
          , envLLVMArchVals = llvmVals
          , envExtensions = exts
          , envPCRegion = pcRegion
          , envMemTraceVar = mvar
          , envBlockEndVar = bvar
          , envLogger = logAction
          , envConfig = vcfg
          , envValidSym = PS.Sym symNonce sym bak
          , envStartTime = startedAt
          , envCurrentFrame = mempty
          , envPathCondition = mempty
          , envNonceGenerator = gen
          , envParentNonce = Some topNonce
          , envUndefPointerOps = undefops
          , envParentBlocks = mempty
          , envEqCondFns = mempty
          , envExitPairsCache = ePairCache
          , envStatistics = statsVar
          , envOverrides = \ovCfg -> M.fromList [ (n, ov)
                                                | ov@(PVO.SomeOverride o) <- PVOL.overrides ovCfg
                                                , let txtName = WF.functionName (PVO.functionName o)
                                                , n <- [PSym.LocalSymbol txtName, PSym.PLTSymbol txtName]
                                                ]
          , envTreeBuilder = treeBuilder
          , envResetTraceTree = resetSomeTreeBuilder (PC.cfgTraceTree vcfg)
          , envSatCacheRef = satCache
          , envUnsatCacheRef = unsatCache
          , envTargetEquivRegs = targetRegs
          , envPtrAssertions = ptrAsserts
          }
    -- Note from above: we are installing overrides for each override that cover
    -- both local symbol definitions and the corresponding PLT stubs for each
    -- override so that they cover both statically linked and dynamically-linked
    -- function calls.

    (result, stats) <- PSP.runVerificationLoop env pPairs'
    finalizeTree treeBuilder
    endTime <- TM.getCurrentTime
    let duration = TM.diffUTCTime endTime startTime
    IO.liftIO $ LJ.writeLog logAction (PE.AnalysisEnd stats duration)
    return result


unpackBlockData ::
  forall arch bin.
  HasCallStack =>
  PBi.KnownBinary bin =>
  PA.ValidArch arch =>
  PMC.BinaryContext arch bin ->
  PC.Address ->
  CME.ExceptT PEE.EquivalenceError IO (PB.FunctionEntry arch bin)
unpackBlockData ctxt (PC.Address w) =
  case PM.resolveAbsoluteAddress mem (fromIntegral w) of
    Just segAddr ->
      -- We don't include a symbol for this entry point because we don't really
      -- have one conveniently available.  That name is never actually
      -- referenced, so it doesn't seem too problematic.
      return PB.FunctionEntry { PB.functionSegAddr = segAddr
                              , PB.functionSymbol = Nothing
                              , PB.functionBinRepr = W4.knownRepr
                              , PB.functionIgnored = False
                              , PB.functionEnd = Nothing
                              }
    Nothing -> CME.throwError (PEE.equivalenceError @arch (PEE.LookupNotAtFunctionStart callStack caddr))
  where
    mem = MBL.memoryImage (PMC.binary ctxt)
    caddr = PAd.memAddrToAddr (MM.absoluteAddr (MM.memWord (fromIntegral w)))

data UnpackedPatchData arch =
  UnpackedPatchData { unpackedPairs :: [PB.FunPair arch]
                    , unpackedOrigIgnore :: [(MM.MemWord (MM.ArchAddrWidth arch), Integer)]
                    , unpackedPatchIgnore :: [(MM.MemWord (MM.ArchAddrWidth arch), Integer)]
                    , unpackedEquatedFuncs :: [(PAd.ConcreteAddress arch, PAd.ConcreteAddress arch)]
                    , unpackedObservableMemory :: [(MM.MemWord (MM.ArchAddrWidth arch), Integer)]
                    }

unpackPatchData :: forall arch.
  HasCallStack =>
  PA.ValidArch arch =>
  PPa.PatchPair (PMC.BinaryContext arch) ->
  PC.PatchData ->
  CME.ExceptT PEE.EquivalenceError IO (UnpackedPatchData arch)
unpackPatchData contexts pd =
   do pairs' <-
         DT.forM (PC.patchPairs pd) $
           \(PC.BlockAlignment { PC.originalBlockStart = bd, PC.patchedBlockStart = bd' }) -> PPa.runPatchPairT $ do
            let bdPair = PPa.PatchPairC bd bd'
            PPa.forBins $ \bin -> do
              ctx <- PPa.get bin contexts
              bd_ <- PPa.getC bin bdPair
              CME.lift $ unpackBlockData ctx bd_

      let f (PC.Address w) = PAd.memAddrToAddr (MM.absoluteAddr (MM.memWord (fromIntegral w)))
      let g (PC.GlobalPointerAllocation { PC.pointerAddress = PC.Address loc, PC.blockSize = len}) = (MM.memWord (fromIntegral loc), toInteger len)

      let oIgn' = map g (PC.ignoreOriginalAllocations pd)
      let pIgn' = map g (PC.ignorePatchedAllocations pd)

      let eqFuncs' = [ (f (PC.originalEquatedFunction eqf), f (PC.patchedEquatedFunction eqf))
                     | eqf <- PC.equatedFunctions pd
                     ]

      let obsMem' =  [ ( MM.memWord (fromIntegral addr), toInteger len )
                     | PC.MemRegion (PC.Address addr) len <- PC.observableMemory pd
                     ]

      return UnpackedPatchData { unpackedPairs = pairs'
                               , unpackedOrigIgnore = oIgn'
                               , unpackedPatchIgnore = pIgn'
                               , unpackedEquatedFuncs = eqFuncs'
                               , unpackedObservableMemory = obsMem'
                               }

-- Map every global address pointer into the global memory region
trivialGlobalMap :: W4.SymNat sym -> MS.GlobalMap sym (MT.MemTrace arch) w
trivialGlobalMap globalRegion =
  MS.GlobalMap $ \_ _ _segNum off -> pure (CLM.LLVMPointer globalRegion off)
