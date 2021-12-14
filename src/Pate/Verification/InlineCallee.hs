{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Pate.Verification.InlineCallee ( inlineCallee ) where

import           Control.Lens ( (&), (%~), (^.) )
import qualified Control.Lens as L
import           Control.Monad (foldM)
import qualified Control.Monad.Catch as CMC
import qualified Control.Monad.Except as CME
import qualified Control.Monad.Reader as CMR
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import           Data.Parameterized.Some ( Some(..) )
import           Data.Parameterized.SymbolRepr ( knownSymbol )
import           Data.Proxy ( Proxy(..) )
import           Data.String ( fromString )
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits ( type (<=) )
import qualified System.IO as IO

import qualified Data.Macaw.Architecture.Info as DMAI
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Symbolic.Memory as DMSM
import qualified Data.Macaw.Types as DMT
import qualified Lang.Crucible.Analysis.Postdom as LCAP
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.CFG.Core as CCC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.Bytes as LCLB
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.Intrinsics as LCLI
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.GlobalState as LCSG
import qualified Lang.Crucible.Simulator.Intrinsics as LCSI
import qualified Lang.Crucible.Simulator.OverrideSim as LCSO
import qualified Lang.Crucible.Simulator.PathSatisfiability as LCSP
import qualified Lang.Crucible.Types as LCT
import qualified What4.BaseTypes as WT
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WP
import qualified What4.Protocol.Online as WPO
import qualified What4.Symbol as WS

import qualified Pate.Address as PAd
import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PCo
import           Pate.Equivalence as PEq
import qualified Pate.Equivalence.Error as PEE
import qualified Pate.Memory as PM
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.Monad.Environment as PME
import qualified Pate.Panic as PP
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Proof.Operations as PFO
import qualified Pate.Solver as PS


-- | Create a crucible-friendly name for a macaw function
--
-- If there is no symbol associated with the function, use its address as its
-- name.
discoveryFunName
  :: (DMM.MemWidth (DMC.ArchAddrWidth arch))
  => DMD.DiscoveryFunInfo arch ids
  -> WF.FunctionName
discoveryFunName dfi =
  WF.functionNameFromText txt
  where
    txt = TE.decodeUtf8With TEE.lenientDecode (DMD.discoveredFunName dfi)

-- | Construct a Crucible CFG for a macaw function
toCrucibleCFG
  :: (DMM.MemWidth (DMC.ArchAddrWidth arch))
  => DMS.MacawSymbolicArchFunctions arch
  -> DMD.DiscoveryFunInfo arch ids
  -> IO (CCC.SomeCFG (DMS.MacawExt arch)
                     (Ctx.EmptyCtx Ctx.::> LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
                     (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))))
toCrucibleCFG archFns dfi = do
  halloc <- CFH.newHandleAllocator
  let fnName = discoveryFunName dfi
  let posFn = WP.OtherPos . fromString . show
  DMS.mkFunCFG archFns halloc fnName posFn dfi

-- | Allocate an initial simulator value for a given machine register
--
-- Takes an initial stack register value
--
-- FIXME: This currently allocates all symbolic state. We want to take any
-- concrete values we can from the callers context.
mkInitialRegVal
  :: ( LCB.IsSymInterface sym
     , DMT.HasRepr (DMC.ArchReg arch) DMT.TypeRepr
     , PA.ValidArch arch
     , HasCallStack
     )
  => DMS.MacawSymbolicArchFunctions arch
  -> sym
  -> LCS.RegValue sym (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
  -> DMC.ArchReg arch tp
  -> IO (LCS.RegValue' sym (DMS.ToCrucibleType tp))
mkInitialRegVal symArchFns sym sp_val r
  | Just PC.Refl <- PC.testEquality r DMC.sp_reg = return (LCS.RV sp_val)
  | otherwise = do
    let regName = DMS.crucGenArchRegName symArchFns r
    case DMT.typeRepr r of
      DMT.BoolTypeRepr -> LCS.RV <$> WI.freshConstant sym regName WT.BaseBoolRepr
      DMT.BVTypeRepr w -> do
        c <- WI.freshConstant sym regName (WT.BaseBVRepr w)
        LCS.RV <$> LCLM.llvmPointer_bv sym c
      DMT.TupleTypeRepr PL.Nil -> return (LCS.RV Ctx.Empty)
      DMT.TupleTypeRepr _ ->
        PP.panic PP.InlineCallee "mkInitialRegVal" ["Tuple types are not supported initial register values"]
      DMT.FloatTypeRepr _ ->
        PP.panic PP.InlineCallee "mkInitialRegVal" ["Floating point types are not supported initial register values"]
      DMT.VecTypeRepr {} ->
        PP.panic PP.InlineCallee "mkInitialRegVal" ["Vector types are not supported initial register values"]

stackSizeBytes :: Integer
stackSizeBytes = 1024 * 2

stackInitialOffset :: Integer
stackInitialOffset = 1024

-- | Allocate a stack in a fresh region, returning the 1. updated memory impl and
-- 2. the value of the initial stack pointer
allocateStack
  :: ( LCB.IsSymInterface sym
     , PA.ValidArch arch
     , w ~ DMC.ArchAddrWidth arch
     , 16 <= w
     )
  => proxy arch
  -> sym
  -> LCLM.MemImpl sym
  -> IO (LCLM.MemImpl sym, LCS.RegValue sym (LCLM.LLVMPointerType w))
allocateStack _proxy sym mem0 = do
  let ?recordLLVMAnnotation = \_ _ -> return ()
  stackArrayStorage <- WI.freshConstant sym (WS.safeSymbol "stack_array") WI.knownRepr
  stackSizeBV <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackSizeBytes)
  let ?ptrWidth = WI.knownRepr
  (stackBasePtr, mem1) <- LCLM.doMalloc sym LCLM.StackAlloc LCLM.Mutable "stack_alloc" mem0 stackSizeBV LCLD.noAlignment
  mem2 <- LCLM.doArrayStore sym mem1 stackBasePtr LCLD.noAlignment stackArrayStorage stackSizeBV

  stackInitialOffsetBV <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr stackInitialOffset)
  sp <- LCLM.ptrAdd sym WI.knownRepr stackBasePtr stackInitialOffsetBV
  return (mem2, sp)

allocateIgnorableRegions
  :: ( LCB.IsSymInterface sym
     , PA.ValidArch arch
     , w ~ DMC.ArchAddrWidth arch
     , 16 <= w
     )
  => proxy arch
  -> sym
  -> LCLM.MemImpl sym
  -> [(DMM.MemWord (DMC.ArchAddrWidth arch), Integer)]
  -> IO (LCLM.MemImpl sym, [LCLM.LLVMPtr sym w])
allocateIgnorableRegions _proxy sym mem0 = foldM allocateIgnPtr (mem0,mempty)
  where
    allocateIgnPtr (mem,ptrs) (loc, len) =
      do let ?recordLLVMAnnotation = \_ _ -> return ()
         let ?ptrWidth = WI.knownRepr

         -- allocate a heap region region 
         len' <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr len)
         (ptr, mem1) <- LCLM.doMalloc sym LCLM.HeapAlloc LCLM.Mutable "ignorable_region" mem len' LCLD.noAlignment

         -- poke the pointer to that region into the global memory at the correct location
         let locBits = BVS.mkBV WI.knownRepr (DMM.memWordToUnsigned loc)
         locPtr <- LCLM.llvmPointer_bv sym =<< WI.bvLit sym WI.knownRepr locBits
         let st = LCLM.bitvectorType (LCLB.bitsToBytes (WI.intValue ?ptrWidth))
         mem2 <- LCLM.storeRaw sym mem1 locPtr st LCLD.noAlignment (LCLM.ptrToPtrVal ptr)

         -- write a backing array of fresh bytes into the region
         regionArrayStorage <- WI.freshConstant sym (WS.safeSymbol "ignorable_region_array") WI.knownRepr
         mem3 <- LCLM.doArrayStore sym mem2 ptr LCLD.noAlignment regionArrayStorage len'

         return (mem3, (ptr:ptrs))

toCrucibleEndian :: DMM.Endianness -> LCLD.EndianForm
toCrucibleEndian macawEnd =
  case macawEnd of
    DMM.LittleEndian -> LCLD.LittleEndian
    DMM.BigEndian -> LCLD.BigEndian

-- | Allocate an initial register and memory state for the symbolic execution step
--
-- NOTE: The same initial state should be used for both functions, to ensure
-- that the post-states are comparable.
--
-- NOTE: The memory setup is currently taken from the original binary. The
-- patched binary could technically have a different initial state that we do
-- not account for right now. It is not clear how to reconcile the two if they
-- are different. The best approach is probably to compute a sound
-- over-approximation of the available memory.
allocateInitialState
  :: forall arch sym w
   . ( LCB.IsSymInterface sym
     , w ~ DMC.ArchAddrWidth arch
     , 16 <= w
     , PA.ValidArch arch
     , PA.ArchConstraints arch
     )
  => DMS.MacawSymbolicArchFunctions arch
  -> sym
  -> DMAI.ArchitectureInfo arch
  -> DMM.Memory w
  -> IO ( LCS.RegEntry sym (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
        , LCLM.MemImpl sym
        , DMSM.MemPtrTable sym w
        )
allocateInitialState symArchFns sym archInfo memory = do
  let ?recordLLVMAnnotation = \_ _ -> return ()
  let proxy = Proxy @arch
  let crucRegTypes = DMS.crucArchRegTypes symArchFns
  let regsRepr = LCT.StructRepr crucRegTypes

  let endianness = toCrucibleEndian (DMAI.archEndianness archInfo)
  -- Treat all mutable values in the global memory as symbolic
  --
  -- This is the safer strategy in this case, since we don't have any of the
  -- context of the program before this function, so any mutable memory
  -- locations could theoretically have any value. This could be problematic if
  -- it causes global state to be under-constrained; safely handling this is
  -- complicated, and would require significant infrastructure in the rest of
  -- the verifier to propagate known facts.
  let memModelContents = DMSM.SymbolicMutable
  (mem0, memPtrTbl) <- DMSM.newGlobalMemory proxy sym endianness memModelContents memory

  (mem1, sp) <- allocateStack proxy sym mem0
  initialRegisters <- liftIO $ DMS.macawAssignToCrucM (mkInitialRegVal symArchFns sym sp) (DMS.crucGenRegAssignment symArchFns)
  let initialRegsEntry = LCS.RegEntry regsRepr initialRegisters

  return (initialRegsEntry, mem1, memPtrTbl)

data GlobalStateError = Timeout
                      | AbortedExit


getFinalGlobalValue
  :: (LCS.RegValue sym LCT.BoolType -> LCS.RegValue sym tp -> LCS.RegValue sym tp -> IO (LCS.RegValue sym tp))
  -> LCS.GlobalVar tp
  -> LCS.ExecResult p sym ext u
  -> IO (Either GlobalStateError (LCS.RegValue sym tp))
getFinalGlobalValue mergeBranches global execResult = CME.runExceptT $ do
  case execResult of
    LCS.AbortedResult _ res -> handleAbortedResult res
    LCS.FinishedResult _ res ->
      case res of
        LCS.TotalRes gp -> return (getValue global gp)
        LCS.PartialRes _ cond gp abortedRes -> do
          let value = getValue global gp
          onAbort <- handleAbortedResult abortedRes
          CME.lift $ mergeBranches cond value onAbort
    LCS.TimeoutResult {} -> CME.throwError Timeout
  where
    handleAbortedResult res =
      case res of
        LCS.AbortedExec _ gp -> return (getValue global gp)
        LCS.AbortedBranch _ cond onOK onAbort -> do
          okVal <- handleAbortedResult onOK
          abortVal <- handleAbortedResult onAbort
          CME.lift $ mergeBranches cond okVal abortVal
        LCS.AbortedExit {} -> CME.throwError AbortedExit
    getValue glob gp =
      case LCSG.lookupGlobal glob (gp ^. LCS.gpGlobals) of
        Just value -> value
        Nothing ->
          -- This case is a programming error (the requested global was
          -- expected), so we can fail loudly
          PP.panic PP.InlineCallee "getFinalGlobalValue" ["Missing expected global: " ++ show glob]

-- | The mux operation for the global memory state
--
-- Note that we pass in an empty set of intrinsic types here; this happens to be
-- fine for LLVM_memory, as its implementation of the mux operation ignores that
-- argument.
muxMemImpl :: (LCB.IsSymInterface sym) => sym -> LCS.RegValue sym LCT.BoolType -> LCLM.MemImpl sym -> LCLM.MemImpl sym -> IO (LCLM.MemImpl sym)
muxMemImpl sym = LCSI.muxIntrinsic sym LCSI.emptyIntrinsicTypes (knownSymbol @"LLVM_memory") Ctx.empty

-- | We do not actually want to check the validity of pointer operations in this
-- part of the verifier. We have no particular reason to believe that functions
-- we are verifying are memory safe. We just want to relate the behaviors of the
-- pre- and post-patch programs.
--
-- Never generate additional validity assertions
validityCheck :: DMS.MkGlobalPointerValidityAssertion sym w
validityCheck _ _ _ _ = return Nothing

-- | A convenient Lens-styled combinator for updating a 'LCSO.FnBinding'
insertFnBinding
  :: LCSO.FnBinding p sym ext
  -> LCS.FunctionBindings p sym ext
  -> LCS.FunctionBindings p sym ext
insertFnBinding (LCS.FnBinding h s) m =
  LCS.FnBindings (CFH.insertHandleMap h s (LCS.fnBindings m))

data IncrementalDiscoveryError where
  CannotResolveSegmentFor :: BVS.BV w -> IncrementalDiscoveryError

deriving instance Show IncrementalDiscoveryError

-- | Given a function address as a raw bitvector, convert it into a
-- 'PB.ConcreteBlock' (which, despite the name, doesn't include any code data or
-- metadata - it is basically just a wrapper around the address)
--
-- Note that we are converting the raw bitvector to an address without special
-- regard for the region that would appear in a MemSegmentOff. All code
-- addresses are in region 0 in the memory model we set up for machine code
-- symbolic execution (in large part because they are constructed from literals
-- in the binary with no associated region).
concreteBlockFromBVAddr
  :: forall w arch bin proxy
   . ( w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     )
  => proxy arch
  -> PBi.WhichBinaryRepr bin
  -> DMM.Memory w
  -> BVS.BV w
  -> Either IncrementalDiscoveryError (PB.ConcreteBlock arch bin)
concreteBlockFromBVAddr _proxy binRepr mem bv =
  case PM.resolveAbsoluteAddress mem addrWord of
    Nothing -> Left (CannotResolveSegmentFor bv)
    Just segOff -> do
      let fn = PB.FunctionEntry { PB.functionSegAddr = segOff
                                , PB.functionSymbol = Nothing
                                , PB.functionBinRepr = binRepr
                                }
      return PB.ConcreteBlock { PB.concreteAddress = addr
                              , PB.concreteBlockEntry = PB.BlockEntryInitFunction
                              , PB.blockBinRepr = binRepr
                              , PB.blockFunctionEntry = fn
                              }

  where
    addrWord :: DMM.MemWord w
    addrWord = fromIntegral (BVS.asUnsigned bv)
    addr :: PAd.ConcreteAddress arch
    addr = PAd.memAddrToAddr (DMM.absoluteAddr addrWord)

-- | Given a register state corresponding to a function call, use the
-- instruction pointer to look up the called function and return an appropriate
-- function handle.
--
-- This function is able to update the Crucible state, which we use to do
-- incremental code discovery (only binding function handles and doing code
-- discovery on demand).
lookupFunction
  :: forall sym arch bin mem binFmt
   . ( PA.ValidArch arch
     , LCB.IsSymInterface sym
     , PBi.KnownBinary bin
     )
  => PMC.ParsedFunctionMap arch bin
  -> DMS.GenArchVals mem arch
  -> MBL.LoadedBinary arch binFmt
  -> DMS.LookupFunctionHandle sym arch
lookupFunction pfm archVals loadedBinary = DMS.LookupFunctionHandle $ \crucState _mem0 regs -> do
  let sym = crucState ^. LCS.stateContext . LCS.ctxSymInterface
  let regsRepr = LCT.StructRepr (DMS.crucArchRegTypes (DMS.archFunctions archVals))
  let regsEntry = LCS.RegEntry regsRepr regs
  let ipPtr = DMS.lookupReg archVals regsEntry DMC.ip_reg
  ipBV <- LCLM.projectLLVM_bv sym (LCS.regValue ipPtr)
  case WI.asBV ipBV of
    Nothing -> PP.panic PP.InlineCallee "lookupFunction" ["Non-constant target IP for call: " ++ show (WI.printSymExpr ipBV)]
    Just bv ->
      case concreteBlockFromBVAddr (Proxy @arch) PC.knownRepr (MBL.memoryImage loadedBinary) bv of
        -- FIXME: This should probably be an exception, rather than a panic
        --
        -- It is plausible that a user could feed us a binary that triggered
        -- this (it would be a very strange and probably bad binary, but still
        -- externally triggerable)
        Left err -> PP.panic PP.InlineCallee "lookupFunction" ["Error while interpreting instruction pointer: " ++ show err]
        Right blk -> do
          -- FIXME: Here we are decoding the function at the given address in our
          -- binary. We need to also take in a symbol table to let us identify
          -- external calls (or calls to named functions) that we might have
          -- overrides for.
          mdfi <- PMC.parsedFunctionContaining blk pfm
          case mdfi of
            -- FIXME: This probably shouldn't be a panic - rather an exception, or perhaps an uninterpreted effect
            Nothing -> PP.panic PP.InlineCallee "lookupFunction" ["Unable to find mapping for address " ++ show bv]
            Just (Some dfi) -> do
              CCC.SomeCFG cfg <- toCrucibleCFG (DMS.archFunctions archVals) dfi
              -- Return a 'FnHandle' and an updated 'CrucibleState'

              -- We could thread the handle allocator through, but it actually has
              -- no data now, so allocating one is essentially free and doesn't have
              -- any correctness downsides
              let halloc = crucState ^. LCS.stateContext . L.to LCS.simHandleAllocator
              hdl <- CFH.mkHandle' halloc (discoveryFunName dfi) (Ctx.singleton regsRepr) regsRepr

              let fnState = LCS.UseCFG cfg (LCAP.postdomInfo cfg)
              let fnBinding = LCS.FnBinding hdl fnState
              let crucState' = crucState & LCS.stateContext . LCS.functionBindings %~ insertFnBinding fnBinding
              return (hdl, crucState')

-- | Symbolically execute a macaw function with a given initial state, returning
-- the final memory state
--
-- Note that we have to pass in a 'DSM.ArchVals' because the one in 'EquivM' has
-- a different type parameter for the memory model than what we want to use for
-- this symbolic execution.
symbolicallyExecute
  :: forall arch sym ids scope solver fs sym' w bin binFmt
   . ( sym ~ LCBO.OnlineBackend scope solver fs
     , LCB.IsSymInterface sym
     , WPO.OnlineSolver solver
     , w ~ DMC.ArchAddrWidth arch
     , PBi.KnownBinary bin
     )
  => DMS.ArchVals arch
  -> sym
  -> PBi.WhichBinaryRepr bin
  -> MBL.LoadedBinary arch binFmt
  -> DMD.DiscoveryFunInfo arch ids
  -> LCS.RegEntry sym (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
  -- ^ Initial registers to simulate with
  -> LCLM.MemImpl sym
  -- ^ Initial memory to simulate with
  -> DMSM.MemPtrTable sym w
  -> EquivM sym arch (Either GlobalStateError (LCLM.MemImpl sym), [LCLM.LLVMPtr sym w])
symbolicallyExecute archVals sym binRepr loadedBin dfi initRegs initMem memPtrTbl = do
  let ?recordLLVMAnnotation = \_ _ -> return ()

  let symArchFns = DMS.archFunctions archVals
  let crucRegTypes = DMS.crucArchRegTypes symArchFns
  let regsRepr = LCT.StructRepr crucRegTypes

  CCC.SomeCFG cfg <- liftIO $ toCrucibleCFG symArchFns dfi
  let arguments = LCS.RegMap (Ctx.singleton initRegs)
  let simAction = LCS.runOverrideSim regsRepr (LCS.regValue <$> LCS.callCFG cfg arguments)

  halloc <- liftIO $ CFH.newHandleAllocator
  memVar <- liftIO $ LCLM.mkMemVar (T.pack "pate-verifier::memory") halloc

  ignPtrs <- case binRepr of
               PBi.OriginalRepr -> PMC.originalIgnorePtrs . PME.envCtx <$> CMR.ask
               PBi.PatchedRepr  -> PMC.patchedIgnorePtrs  . PME.envCtx <$> CMR.ask
  (initMem', ignorableRegions) <- liftIO $ allocateIgnorableRegions archVals sym initMem ignPtrs

  let globals = LCSG.insertGlobal memVar initMem' LCS.emptyGlobals
  let globalMap = DMSM.mapRegionPointers memPtrTbl

  pfm <- PMC.parsedFunctionMap <$> getBinCtx' binRepr

  DMS.withArchEval archVals sym $ \archEvalFn -> do
    let doLookup = lookupFunction pfm archVals loadedBin
    let extImpl = DMS.macawExtensions archEvalFn memVar globalMap doLookup validityCheck
    -- We start with no handles bound for crucible; we'll add them dynamically
    -- as we find callees via lookupHandle
    --
    -- NOTE: This may need an initial set of overrides
    let fnBindings = LCS.FnBindings CFH.emptyHandleMap
    -- Note: the 'Handle' here is the target of any print statements in the
    -- Crucible CFG; we shouldn't have any, but if we did it would be better to
    -- capture the output over a pipe.
    let ctx = LCS.initSimContext sym LCLI.llvmIntrinsicTypes halloc IO.stdout fnBindings extImpl DMS.MacawSimulatorState
    let s0 = LCS.InitialState ctx globals LCS.defaultAbortHandler regsRepr simAction

    psf <- liftIO $ LCSP.pathSatisfiabilityFeature sym (LCBO.considerSatisfiability sym)
    let execFeatures = [psf]
    let executionFeatures = fmap LCS.genericToExecutionFeature execFeatures
    res <- liftIO $ LCS.executeCrucible executionFeatures s0
    finalMem <- liftIO $ getFinalGlobalValue (muxMemImpl sym) memVar res
    return (finalMem, ignorableRegions)

-- | Look up the macaw CFG for the given function address
--
-- Throws an exception if the function cannot be found
functionFor
  :: forall bin arch sym
   . (PBi.KnownBinary bin)
  => PB.ConcreteBlock arch bin
  -> EquivM sym arch (Some (DMD.DiscoveryFunInfo arch))
functionFor pb = do
  ctx <- getBinCtx
  mdfi <- liftIO $ PMC.parsedFunctionContaining pb (PMC.parsedFunctionMap ctx)
  case mdfi of
    Just sdfi -> return sdfi
    Nothing ->
      let addr = PB.concreteAddress pb
          repr = PC.knownRepr @_ @_ @bin
      in CMC.throwM (PEE.equivalenceErrorFor repr (PEE.MissingExpectedEquivalentFunction addr))

-- | Analyze the post memory states to compute the separation frame for the inlined calls.
buildCallFrame
  :: LCLM.MemImpl sym -- ^ Memory pre state
  -> (LCLM.MemImpl sym, [LCLM.LLVMPtr sym (DMD.ArchAddrWidth arch)])
       -- ^ Original binary post state and ignorable region base pointers
  -> (LCLM.MemImpl sym, [LCLM.LLVMPtr sym (DMD.ArchAddrWidth arch)])
       -- ^ Patched binary post state and ignorable region base pointers
  -> EquivM sym arch (StatePredSpec sym arch)
buildCallFrame initMem (oPostMem,oIgnPtrs) (pPostMem,pIgnPtrs) = undefined

-- | Symbolically execute the given callees and synthesize a new 'PES.StatePred'
-- for the two equated callees (as directed by the user) that only reports
-- memory effects that are not explicitly ignored.
--
-- Unlike the normal loop of 'provePostcondition', this path effectively inlines
-- callees (rather than breaking them into slices compositionally) to produce
-- monolithic summaries. The main goal of this is to enable us to more
-- accurately capture all of the memory effects of the two functions.  This
-- function uses the standard implementation of symbolic execution of machine
-- code provided by macaw-symbolic, rather than the slice-based decomposition.
--
-- The premise is that the two callees (in the original and patched binaries)
-- are actually quite different, but the user would like to reason about their
-- unintended effects.
inlineCallee
  :: forall arch sym
   . (HasCallStack)
  => StatePredSpec sym arch
  -> PPa.BlockPair arch
  -> EquivM sym arch (StatePredSpec sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
inlineCallee contPre pPair = withValid $ withSym $ \sym -> do
  -- Normally we would like to treat errors leniently and continue on in a degraded state
  --
  -- However, if the user has specifically asked for two functions to be equated
  -- and we can't find them, we will just call that a fail-stop error (i.e.,
  -- 'functionFor' can throw an exception).
  Some oDFI <- functionFor @PBi.Original (PPa.pOriginal pPair)
  Some pDFI <- functionFor @PBi.Patched (PPa.pPatched pPair)

  origBinary <- PMC.binary <$> getBinCtx' PBi.OriginalRepr
  patchedBinary <- PMC.binary <$> getBinCtx' PBi.PatchedRepr
  let origMemory = MBL.memoryImage origBinary
  let archInfo = PA.binArchInfo origBinary


  -- Note that we need to get a different archVals here - we can't use the one
  -- in the environment because it is fixed to a different memory model - the
  -- trace based memory model. We need to use the traditional LLVM memory model
  -- for this part of the verifier.
  let archVals = undefined

  -- We allocate a shared initial state to execute both functions on so that we
  -- can compare their final memory states
  let symArchFns = DMS.archFunctions archVals
  (initRegs, initMem, memPtrTbl) <- liftIO $ allocateInitialState @arch symArchFns sym archInfo origMemory

  (eoPostMem, oIgnPtrs) <-
     symbolicallyExecute archVals sym PBi.OriginalRepr origBinary oDFI initRegs initMem memPtrTbl
  (epPostMem, pIgnPtrs) <-
     symbolicallyExecute archVals sym PBi.PatchedRepr patchedBinary pDFI initRegs initMem memPtrTbl

  -- Note: we are symbolically executing both functions to get their memory
  -- post states. We explicitly do *not* want to try to prove all of their
  -- memory safety side conditions (or any other side conditions), since we
  -- can't really assume that either program is correct. We *only* care about
  -- their differences in observable behavior.
  --
  -- In addition to memory, we could *also* collect a symbolic sequence of
  -- observable effects in each function and attempt to prove that those
  -- sequences are the same.

  case (eoPostMem, epPostMem) of
    -- FIXME: In the error cases, generate a default frame and a proof error node
    (Right oPostMem, Right pPostMem) -> do
      statePredSpec <- buildCallFrame initMem (oPostMem, oIgnPtrs) (pPostMem,pIgnPtrs)

      let prfNode = PF.ProofInlinedCall { PF.prfInlinedCallees = pPair
                                        }
      lproof <- PFO.lazyProofApp prfNode
      return (statePredSpec, lproof)
