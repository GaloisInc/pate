{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.Discovery.ParsedFunctions (
    ParsedFunctionMap
  , persistenceDir
  , newParsedFunctionMap
  , parsedFunctionContaining
  , parsedBlocksContaining
  , parsedBlockEntry
  , isFunctionStart
  , findFunctionByName
  , resolveFunctionEntry
  , ParsedBlocks(..)
  , addOverrides
  , addExtraTarget
  , getExtraTargets
  , addExtraEdges
  , isUnsupportedErr
  ) where


import           Control.Lens ( (^.), (&), (.~) )
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Foldable as F
import qualified Data.IORef as IORef
import qualified Data.Map as Map
import qualified Data.Map.Merge.Strict as Map
import           Data.Maybe ( mapMaybe, listToMaybe, fromMaybe, isJust )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..), viewSome )
import qualified Data.Set as Set
import qualified Prettyprinter as PP
import qualified Prettyprinter.Render.Text as PPT
import qualified System.Directory as SD
import           System.FilePath ( (</>), (<.>) )
import qualified System.IO as IO

import qualified Data.Macaw.AbsDomain.AbsState as DMAA
import qualified Data.Macaw.AbsDomain.JumpBounds as DMAJ
import qualified Data.Macaw.Architecture.Info as MAI
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Discovery.State as MD
import qualified Data.Macaw.Discovery.ParsedContents as DMDP
import qualified What4.Interface as W4

import qualified Pate.Address as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Memory as PM
import           Pate.Discovery.PLT (extraJumpClassifier, extraReturnClassifier, ExtraJumps, ExtraJumpTarget(..), extraCallClassifier, extraTailCallClassifier)

import           Pate.TraceTree
import Control.Monad.IO.Class (liftIO)
import Control.Monad (forM)

import Debug.Trace
import Control.Applicative ((<|>))
import Data.Macaw.Utils.IncComp (incCompResult)
import qualified Data.Text as T

data ParsedBlocks arch = forall ids. ParsedBlocks [MD.ParsedBlock arch ids]

data ParsedFunctionState arch bin =
  ParsedFunctionState { parsedFunctionCache :: Map.Map (PB.FunctionEntry arch bin) (Some (MD.DiscoveryFunInfo arch))
                      , discoveryState :: MD.DiscoveryState arch
                      , extraTargets :: Set.Set (MM.ArchSegmentOff arch)
                      , extraEdges :: ExtraJumps arch
                      }



-- | A (lazily constructed) map of function entry points to the blocks for that function
--
-- Think of this as a cache of discovered functions, with some of the extra
-- macaw metadata (e.g., the enclosing DiscoveryFunInfo) discarded
data ParsedFunctionMap arch bin =
  ParsedFunctionMap { parsedStateRef :: IORef.IORef (ParsedFunctionState arch bin)
                    -- ^ State that is updated on-demand
                    , persistenceDir :: Maybe FilePath
                    -- ^ The directory to save discovered CFGs to, if present
                    , patchData :: PC.PatchData
                    -- ^ Extra hints provided from the user to guide code discovery
                    --
                    -- The information we use out of this is a list of functions
                    -- that the analysis should ignore. See Note [Ignored
                    -- Functions] for details.
                    , pfmEndMap :: Map.Map (MM.ArchSegmentOff arch) (MM.ArchSegmentOff arch)
                    , initDiscoveryState :: MAI.ArchitectureInfo arch -> MD.DiscoveryState arch
                    , absStateOverrides :: Map.Map (MM.ArchSegmentOff arch) (PB.AbsStateOverride arch)
                    , defaultInitState :: PB.MkInitialAbsState arch
                    , pfmExtractBlockPrecond :: ExtractBlockPrecondFn arch
                    , pfmWrapClassifier :: forall ids . MAI.BlockClassifier arch ids -> MAI.BlockClassifier arch ids
                    }

-- | copied from 'Pate.Arch' and supplied from the 'ValidArch' instance when initialized
type ExtractBlockPrecondFn arch = 
    DMAA.AbsBlockState (MM.ArchReg arch) {- ^ initial state at function entry point -} ->
    MM.ArchSegmentOff arch {- ^ address for this block -} ->
    DMAA.AbsBlockState (MM.ArchReg arch) {- ^ state for this block -} ->
    Maybe (Either String (MM.ArchBlockPrecond arch))


-- | Add an extra intra-procedural target that should appear within this function body
--   NOTE: This is a bit clumsy to do after some blocks have already been produced
addExtraTarget ::
  MM.ArchConstraints arch =>
  ParsedFunctionMap arch bin ->
  MM.ArchSegmentOff arch ->
  IO ()
addExtraTarget pfm tgt = do
  tgts <- getExtraTargets pfm
  case Set.member tgt tgts of
    True -> return ()
    False -> do
      IORef.modifyIORef' (parsedStateRef pfm) $ \st' -> 
        st' { extraTargets = Set.insert tgt (extraTargets st')}
      flushCache pfm

getExtraTargets ::
  ParsedFunctionMap arch bin ->
  IO (Set.Set (MM.ArchSegmentOff arch))
getExtraTargets pfm = do
  st <- IORef.readIORef (parsedStateRef pfm)
  return $ extraTargets st

flushCache ::
  MM.ArchConstraints arch =>
  ParsedFunctionMap arch bin ->
  IO ()
flushCache pfm = do
  st <- IORef.readIORef (parsedStateRef pfm)
  let ainfo = MD.archInfo (discoveryState st)
  IORef.modifyIORef' (parsedStateRef pfm) $ \st' -> 
    st' { parsedFunctionCache = mempty, discoveryState = initDiscoveryState pfm ainfo }

isUnsupportedErr :: T.Text -> Bool
isUnsupportedErr err = 
     T.isPrefixOf "UnsupportedInstruction" err 
  || T.isPrefixOf "TranslationError" err
  || T.isPrefixOf "DecodeError" err

incrementInstrStart ::
  MM.ArchConstraints arch => 
  MM.ArchAddrWord arch -> 
  MM.Stmt arch ids -> 
  MM.Stmt arch ids
incrementInstrStart off = \case
  MM.InstructionStart wd txt -> MM.InstructionStart (wd + off) txt
  x -> x

addTranslationErrorWrapper ::
  forall arch.
  MM.ArchConstraints arch =>
  MAI.DisassembleFn arch ->
  MAI.DisassembleFn arch
addTranslationErrorWrapper f nonceGen start_ initSt_ offset_ = go 5 start_ initSt_ offset_
  where
    -- hop over at most 5 instructions trying to skip over a translation error
    go (0::Int) _start _initSt _offset = f nonceGen start_ initSt_ offset_
    go maxDepth start initSt offset = do
      (blk,sz) <- f nonceGen start initSt offset
      case MAI.blockTerm blk of
        MAI.TranslateError nextSt err -> do
          next <- case MM.incSegmentOff start ((fromIntegral (sz + MM.addrSize start))) of
              Just x -> return x
              Nothing -> error $ show err ++ "\nUnexpected segment end:" ++ (show start) ++ " " ++ show (sz + MM.addrSize start)
          let v = MM.CValue (MM.RelocatableCValue (MM.addrWidthRepr next) (MM.segoffAddr next))
          let nextSt' = nextSt & MM.curIP .~ v
          (blk',sz') <- go (maxDepth-1) next nextSt' (offset - sz)
          let stmts' = map (incrementInstrStart (fromIntegral (sz + MM.addrSize start))) (MAI.blockStmts blk')
          return $ (MAI.Block (MAI.blockStmts blk ++ [MM.Comment err] ++ stmts') (MAI.blockTerm blk'), sz + sz')
        _ -> return (blk,sz)

overrideDisassembler ::
  MM.ArchConstraints arch =>
  MM.ArchSegmentOff arch ->
  MAI.ArchitectureInfo arch ->
  MAI.ArchitectureInfo arch
overrideDisassembler tgt ainfo = ainfo { 
  MAI.disassembleFn = \nonceGen start initSt offset -> do
    case MM.diffSegmentOff tgt start of
      Just offset' | start <= tgt, offset' <= fromIntegral offset ->
        MAI.disassembleFn ainfo nonceGen start initSt (fromIntegral offset' - 1)
      _ -> MAI.disassembleFn ainfo nonceGen start initSt offset
  }

-- FIXME: throw error on clashes? Currently this just arbitrarily picks one
mergeOverrides ::
  MM.ArchConstraints arch =>
  PB.AbsStateOverride arch ->
  PB.AbsStateOverride arch ->
  PB.AbsStateOverride arch
mergeOverrides l r = MapF.mergeWithKey (\_ l' _r' -> (Just l')) id id l r 

addOverrides ::
  forall arch bin.
  MM.ArchConstraints arch =>
  PB.MkInitialAbsState arch ->
  ParsedFunctionMap arch bin ->
  Map.Map (MM.ArchSegmentOff arch) (PB.AbsStateOverride arch) ->
  IO (ParsedFunctionMap arch bin)
addOverrides defaultInit pfm ovs = do
  let new_ovs = Map.merge Map.preserveMissing Map.preserveMissing (Map.zipWithMaybeMatched (\_ l r -> Just (mergeOverrides l r))) ovs (absStateOverrides pfm)
  let new_init = PB.MkInitialAbsState $ \mem segOff -> mergeOverrides (PB.mkInitAbs defaultInit mem segOff) (PB.mkInitAbs (defaultInitState pfm) mem segOff) 
  return $ pfm { absStateOverrides = new_ovs, defaultInitState = new_init }

addExtraEdges ::
  forall arch bin.
  MM.ArchConstraints arch =>
  ParsedFunctionMap arch bin ->
  ExtraJumps arch ->
  IO ()
addExtraEdges pfm es = do
  mapM_ addTgt (Map.elems es)
  IORef.modifyIORef' (parsedStateRef pfm) $ \st' -> 
    st' { extraEdges = Map.merge Map.preserveMissing Map.preserveMissing (Map.zipWithMaybeMatched (\_ l r -> Just (l <> r))) es (extraEdges st')}
  where
    addTgt :: ExtraJumpTarget arch -> IO ()
    addTgt = \case
      DirectTargets es' -> mapM_ (addExtraTarget pfm) (Set.toList es')
      -- we need to flush the cache here to ensure that we re-check the block at the
      -- call site(s) after adding this as a return
      ReturnTarget -> flushCache pfm
      -- a call shouldn't require special treatment since it won't introduce
      -- any edges
      DirectCall{} -> return ()

-- | Apply the various overrides to the architecture definition before returning the discovery state
getDiscoveryState ::
  forall arch bin.
  MM.ArchConstraints arch =>
  MM.ArchSegmentOff arch {- ^ address of function entry point -} ->
  ParsedFunctionMap arch bin ->
  ParsedFunctionState arch bin ->
  MD.DiscoveryState arch
getDiscoveryState fnaddr pfm st = let
  ainfo0 = MD.archInfo (discoveryState st)

  ainfo1 = foldr overrideDisassembler ainfo0 (extraTargets st)

  ainfo2 = ainfo1 { MAI.mkInitialAbsState = \mem segOff -> let 
    initAbsSt = MAI.mkInitialAbsState ainfo1 mem segOff
    in case Map.lookup segOff (absStateOverrides pfm) of
      Just ov -> applyOverride ov initAbsSt
      Nothing -> applyOverride (PB.mkInitAbs (defaultInitState pfm) mem segOff) initAbsSt
  }
  fnAbsSt = MAI.mkInitialAbsState ainfo2 (MD.memory (discoveryState st)) fnaddr
  extractPrecondFn = \segOff absSt -> case pfmExtractBlockPrecond pfm fnAbsSt segOff absSt of
    Just a -> a
    Nothing -> MAI.extractBlockPrecond ainfo2 segOff absSt
  ainfo3 = ainfo2 { MAI.extractBlockPrecond = extractPrecondFn }

  -- TODO: apply some intelligence here to distinguish direct jumps from tail calls,
  -- for the moment our infrastructure handles direct jumps better, so we prefer that
  ainfo4 = ainfo3 { MAI.archClassifier = pfmWrapClassifier pfm
    (extraCallClassifier (extraEdges st) <|> extraTailCallClassifier (extraEdges st) <|> extraReturnClassifier (extraEdges st))
    }
  ainfo5 = ainfo4 { MAI.disassembleFn = addTranslationErrorWrapper (MAI.disassembleFn ainfo4)}
  in initDiscoveryState pfm ainfo5

getParsedFunctionState ::
  forall arch bin.
  MM.ArchConstraints arch =>
  MM.ArchSegmentOff arch {- ^ address of function entry point -} ->
  ParsedFunctionMap arch bin ->
  IO (ParsedFunctionState arch bin)
getParsedFunctionState fnaddr pfm = do
  st <- IORef.readIORef (parsedStateRef pfm)
  let dst = getDiscoveryState fnaddr pfm st
  return $ st { discoveryState = dst }



-- | Allocate a new empty 'ParsedFunctionMap'
newParsedFunctionMap
  :: MM.ArchConstraints arch =>
     MM.Memory (MM.ArchAddrWidth arch)
  -- ^ The binary memory
  -> MD.AddrSymMap (MM.ArchAddrWidth arch)
  -- ^ Symbols assigned to addresses by metadata
  -> MAI.ArchitectureInfo arch
  -- ^ Architecture-specific code discovery information and configuration
  -> Maybe FilePath
  -- ^ The path to save discovered CFGs to, if present
  -> PC.PatchData
  -- ^ User-provided guidance about the patch structure and verification strategy
  -> Map.Map (MM.ArchSegmentOff arch) (MM.ArchSegmentOff arch)
  -- ^ mapping from function entry points to potential end points
  -> ExtractBlockPrecondFn arch
  -- ^ override for extracing block preconditions
  -> (forall ids . MAI.BlockClassifier arch ids -> MAI.BlockClassifier arch ids)
  -- ^ wrapper for block classifiers
  -> IO (ParsedFunctionMap arch bin)
newParsedFunctionMap mem syms archInfo mCFGDir pd fnEndMap fnExtractPrecond blockClassifiers = do
  let ds0 = MD.emptyDiscoveryState mem syms archInfo
  let s0 = ParsedFunctionState { parsedFunctionCache = mempty
                               , discoveryState = ds0
                               , extraTargets = mempty
                               , extraEdges = mempty
                               }
  ref <- IORef.newIORef s0
  return ParsedFunctionMap { parsedStateRef = ref
                           , persistenceDir = mCFGDir
                           , patchData = pd
                           , pfmEndMap = fnEndMap
                           , initDiscoveryState = MD.emptyDiscoveryState mem syms
                           , absStateOverrides = mempty
                           , defaultInitState = PB.defaultMkInitialAbsState
                           , pfmExtractBlockPrecond = fnExtractPrecond
                           , pfmWrapClassifier = blockClassifiers
                           }

funInfoToFunEntry ::
  PBi.WhichBinaryRepr bin ->
  MD.DiscoveryFunInfo arch ids ->
  ParsedFunctionMap arch bin ->
  Set.Set (MM.MemSegmentOff (MM.ArchAddrWidth arch)) ->
  PB.FunctionEntry arch bin
funInfoToFunEntry binRepr dfi pfm ignoredAddrs =
  PB.FunctionEntry
  { PB.functionSegAddr = MD.discoveredFunAddr dfi
  , PB.functionSymbol  = fmap PB.mkFunctionSymbol (MD.discoveredFunSymbol dfi)
  , PB.functionBinRepr = binRepr
  , PB.functionIgnored = Set.member (MD.discoveredFunAddr dfi) ignoredAddrs
  , PB.functionEnd = Map.lookup (MD.discoveredFunAddr dfi) (pfmEndMap pfm)
  }

buildParsedBlocks :: MD.DiscoveryFunInfo arch ids -> ParsedBlocks arch
buildParsedBlocks dfi = ParsedBlocks (Map.elems (dfi ^. MD.parsedBlocks))

-- | Write the macaw CFG for the given discovered function to disk if we are
-- given a directory to store it in.
--
-- Note that this directory is the *base* directory; we use the type repr for
-- the binary (original vs patched) to ensure that we don't overwrite results
-- from different binaries on disk.
saveCFG
  :: (MM.ArchConstraints arch)
  => Maybe FilePath
  -> PBi.WhichBinaryRepr bin
  -> MD.DiscoveryFunInfo arch ids
  -> IO ()
saveCFG mCFGDir repr dfi =
  F.forM_ mCFGDir $ \cfgDir -> do
    let baseDir = cfgDir </> show repr
    SD.createDirectoryIfMissing True baseDir
    let fname = baseDir </> show (MD.discoveredFunAddr dfi) <.> "cfg"
    IO.withFile fname IO.WriteMode $ \hdl -> do
      PPT.hPutDoc hdl (PP.pretty dfi)

segoffAddrsFor
  :: (MM.MemWidth w)
  => MM.Memory w
  -> PC.Address
  -> Maybe (MM.MemSegmentOff w)
segoffAddrsFor mem (PC.Address w) = do
  PM.resolveAbsoluteAddress mem (fromIntegral w)

-- | An empty macaw function that has no effect on its arguments or memory
--
-- This is meant to be used as a stand-in for any function that the user has
-- specified should be ignored.
emptyFunction
  :: (MM.RegisterInfo (MM.ArchReg arch))
  => MM.MemSegmentOff (MM.ArchAddrWidth arch)
  -- ^ The address of the function entry point
  -> MD.DiscoveryFunInfo arch x
emptyFunction faddr =
  MD.DiscoveryFunInfo { MD.discoveredFunReason = MD.UserRequest
                      , MD.discoveredFunAddr = faddr
                      , MD.discoveredFunSymbol = Nothing
                      , MD._parsedBlocks = Map.singleton faddr emptyBlock
                      , MD.discoveredClassifyFailureResolutions = []
                      }
  where
    retArgs = MM.mkRegState MM.Initial
    emptyBlock = DMDP.ParsedBlock { DMDP.pblockAddr = faddr
                                  , DMDP.blockSize = 4
                                  , DMDP.pblockStmts = []
                                  , DMDP.pblockTermStmt = DMDP.ParsedReturn retArgs
                                  , DMDP.blockReason = DMDP.FunctionEntryPoint
                                  , DMDP.blockAbstractState = DMAA.fnStartAbsBlockState faddr MapF.empty []
                                  , DMDP.pblockPrecond = Left "No block preconditions because this is a synthetic block"
                                  , DMDP.blockJumpBounds = DMAJ.functionStartBounds
                                  }
applyOverride ::
  MM.RegisterInfo (MM.ArchReg arch) =>
  PB.AbsStateOverride arch ->
  DMAA.AbsBlockState (MM.ArchReg arch) ->
  DMAA.AbsBlockState (MM.ArchReg arch)
applyOverride ov absSt = do
  let regSt = absSt ^. DMAA.absRegState
  let regSt' = MM.mapRegsWith (\r val -> case MapF.lookup r ov of
        Just val' -> val'
        _ -> val) regSt
  absSt & DMAA.absRegState .~ regSt'

{-
-- | Modify the discovery state to inject additional abstract state information
--   when analyzing the given function
-- TODO: should setting the abstract state of an already explored function
-- be considered an error? Right now we just delete the corresponding entry in the cache
setAbstractState ::
  MM.ArchConstraints arch =>
  MM.RegisterInfo (MM.ArchReg arch) =>
  PB.MkInitialAbsState arch ->
  PB.ConcreteBlock arch bin ->
  PB.AbsStateOverride arch ->
  ParsedFunctionMap arch bin ->
  IO ()
setAbstractState defaultInit fnEntry absSt (ParsedFunctionMap pfmRef _ _ ovRef initSt) = do
  let faddr = PB.functionSegAddr fnEntry
  let archInfo = MD.archInfo initSt
  ovs <- IORef.readIORef ovRef
  let shouldUpdate = case Map.lookup faddr ovs of
        Just prevAbsSt -> absSt /= prevAbsSt
        Nothing -> True
  case shouldUpdate of
    False -> return ()
    True -> do
      let absSts' = Map.insert faddr absSt ovs

      IORef.writeIORef ovRef absSts'
      let mkAbs segOff preCond = let
            initAbsSt = MAI.initialBlockRegs archInfo segOff preCond 
            --ov = PB.mkInitAbs defaultInit mem segOff
            -- FIXME: we're just using the default override always
            in case Map.lookup segOff absSts' of
              Just ov -> applyOverride ov initAbsSt
              -- FIXME: this is really not safe
              -- FIXME: should we just do this for ignored functions?
              Nothing -> --initAbsSt
                let ov = PB.mkInitAbs defaultInit segOff preCond
                in applyOverride ov initAbsSt
      st <- IORef.readIORef pfmRef
      let
        ainfo' = archInfo{ MAI.mkInitialAbsState = mkInit }
        -- modify the archInfo of the discovery state to
        -- pick up any modified abstract domains
        dst' = MD.setArchInfo ainfo' (discoveryState st)
        funInfo' = dst' ^. MD.funInfo
        dst'' = dst' & MD.funInfo .~ (Map.delete faddr funInfo')
      let cache' = Map.delete fnEntry (parsedFunctionCache st)
      let st' =  st {parsedFunctionCache = cache', discoveryState = dst'' }
      IORef.writeIORef pfmRef st'
-}

getIgnoredFns ::
  forall arch bin.
  MM.ArchConstraints arch =>
  PBi.WhichBinaryRepr bin ->
  ParsedFunctionMap arch bin ->
  IO (Set.Set (MM.MemSegmentOff (MM.ArchAddrWidth arch)))
getIgnoredFns repr (ParsedFunctionMap pfmRef _ pd _ _ _ _ _ _) = do
  st <- IORef.readIORef pfmRef
  let ds0 = discoveryState st
  let mem = MD.memory ds0
  return $
    Set.fromList $ case repr of
      PBi.OriginalRepr -> mapMaybe (segoffAddrsFor mem) (PC.ignoreOriginalFunctions pd)
      PBi.PatchedRepr -> mapMaybe (segoffAddrsFor mem) (PC.ignorePatchedFunctions pd)

-- | Return the 'MD.DiscoveryFunInfo' (raw macaw code discovery artifact)
-- corresponding to the function that contains the given basic block
--
-- This will return a cached parsed function if possible, or run the macaw
-- analysis on a new address and cache the result.
--
-- This function will return 'Nothing' if the address it is provided (via the
-- 'PB.ConcreteBlock') is not a mapped address in the binary. As long as the
-- address is valid, this function will at *least* return a single block with a
-- macaw translation error.
parsedFunctionContaining ::
  forall bin arch .
  (MM.ArchConstraints arch) =>
  PB.ConcreteBlock arch bin ->
  ParsedFunctionMap arch bin ->
  IO (Maybe (Some (MD.DiscoveryFunInfo arch)))
parsedFunctionContaining blk pfm@(ParsedFunctionMap pfmRef mCFGDir _pd _ _ _ _ _ _) = do
  let faddr = PB.functionSegAddr (PB.blockFunctionEntry blk)

  st <- getParsedFunctionState faddr pfm
  ignoredAddresses <- getIgnoredFns (PB.blockBinRepr blk) pfm

  -- First, check if we have a cached set of blocks for this state
  case Map.lookup (PB.blockFunctionEntry blk) (parsedFunctionCache st) of
    Just sdfi -> return (Just sdfi)
    Nothing -> do
      -- Otherwise, run code discovery at this address
      -- NOTE: We are using the strict atomic modify IORef here. The code is
      -- not attempting to force the modified state or returned function to
      -- normal form.
      --
      -- It isn't clear if this will be a problem in practice or not. We
      -- think that the worst case is that we end up with thunks in the
      -- IORef that might be evaluated multiple times if there is a lot of
      -- contention. If that becomes a problem, we may want to change this
      -- to an MVar where we fully evaluate each result before updating it.
      (_, Some dfi) <- return $ atomicAnalysis ignoredAddresses faddr st
      --IORef.writeIORef pfmRef pfm'
      saveCFG mCFGDir (PB.blockBinRepr blk) dfi
      return (Just (Some dfi))
          
  where
    -- The entire analysis is bundled up in here so that we can issue an atomic
    -- update to the cache that preserves the discovery state. If we didn't do
    -- the analysis inside of the atomic update, we might lose updates to the
    -- discovery state. While that is not very important for our use case (we
    -- don't care about the preserved discovery state), it seems morally better
    -- to not lose those updates.
    --
    -- If the address is one that is to be ignored (as specified by the user),
    -- return an empty function (defined above). This empty function is handled
    -- normally by the rest of the verifier, and just produces a proof node with
    -- no interesting effects (thus skipping the ignored function and all of its
    -- callees). Note that by returning it here, the empty function is cached
    -- for the entry point address and reused if needed.
    atomicAnalysis ignoredAddressSet faddr st
      | Set.member faddr ignoredAddressSet = (st, Some (emptyFunction faddr))
      | otherwise =
        let rsn = MD.CallTarget faddr
        in case incCompResult (MD.discoverFunction MD.defaultDiscoveryOptions faddr rsn (discoveryState st) []) of
             (ds2, Some dfi) ->
               let entry = funInfoToFunEntry (PB.blockBinRepr blk) dfi pfm ignoredAddressSet 
               in (st { parsedFunctionCache = Map.insert entry (Some dfi) (parsedFunctionCache st)
                      , discoveryState = ds2
                      }, Some dfi)

segOffCases :: MM.MemWidth w => MM.MemSegmentOff w -> (MM.MemSegmentOff w, MM.MemSegmentOff w)
segOffCases e = fromMaybe (error "segOffCases") $ do
  let e' = MM.clearSegmentOffLeastBit e
  e_hi <- MM.incSegmentOff e' 1
  return (e', e_hi)

resolveFunctionEntry ::
  forall bin arch .
  (MM.ArchConstraints arch) =>
  PB.FunctionEntry arch bin ->
  ParsedFunctionMap arch bin ->
  IO (PB.FunctionEntry arch bin)
resolveFunctionEntry fe pfm@(ParsedFunctionMap pfmRef _ _ fnEndMap _ _ _ _ _) = do
  st <- IORef.readIORef pfmRef
  let syms = MD.symbolNames (discoveryState st)
  ignoredAddresses <- getIgnoredFns (PB.functionBinRepr fe) pfm
  let fe' = fe { PB.functionEnd = Map.lookup (PB.functionSegAddr fe) fnEndMap }
  return $ fromMaybe fe' $ (do
    let (addr_lo, addr_hi) = segOffCases (PB.functionSegAddr fe)
    -- lookup both cases where the low bit is set or unset, since the symbol table
    -- may have one or the other
    nm <- Map.lookup addr_lo syms <|> Map.lookup addr_hi syms
    return $ fe { PB.functionSymbol = Just (PB.mkFunctionSymbol nm)
                , PB.functionIgnored = Set.member (PB.functionSegAddr fe) ignoredAddresses 
                , PB.functionEnd = Map.lookup (PB.functionSegAddr fe) fnEndMap
                }
    )

instance MM.ArchConstraints arch => IsTraceNode '(sym,arch) "parsedblock" where
  type TraceNodeType '(sym,arch) "parsedblock" = Some (MD.ParsedBlock arch)
  prettyNode () (Some pb) = PP.pretty pb
  nodeTags = [(Summary, \() (Some pb) -> PP.viaShow (MD.pblockAddr pb))]

-- | Similar to 'parsedFunctionContaining', except that it constructs the
-- 'ParsedBlocks' structure used in most of the verifier.
parsedBlocksContaining ::
  forall bin arch sym e m.
  (MM.ArchConstraints arch) =>
  IsTreeBuilder '(sym,arch) e m =>
  PB.ConcreteBlock arch bin ->
  ParsedFunctionMap arch bin ->
  m (Maybe (ParsedBlocks arch))
parsedBlocksContaining blk pfm = (liftIO $ parsedFunctionContaining blk pfm) >>= \case
  Just (Some pbs) -> Just <$> do
    ParsedBlocks pbs' <- return $ buildParsedBlocks pbs
    subTree @"parsedblock" "parsedBlocksContaining" $ do
      ParsedBlocks <$> mapM (\pb -> subTrace (Some pb) $ go pb) pbs'
  Nothing -> return Nothing


  where
    go :: MD.ParsedBlock arch ids -> m (MD.ParsedBlock arch ids)
    go pb = return pb

findFunctionByName ::
  (PBi.KnownBinary bin, MM.ArchConstraints arch) =>
  String ->
  ParsedFunctionMap arch bin ->
  IO (Maybe (PB.FunctionEntry arch bin))
findFunctionByName nm pfm = do
  st <- IORef.readIORef (parsedStateRef pfm)
  let syms = Map.toList $ MD.symbolNames (discoveryState st)
  case F.find (\(_addr,nm_) -> BSC.pack nm == nm_) syms of
    Just (addr,nm_) -> do
      let fe = PB.FunctionEntry addr (Just (PB.mkFunctionSymbol nm_)) W4.knownRepr False Nothing
      Just <$> resolveFunctionEntry fe pfm
    Nothing -> return Nothing

isFunctionStart ::
  forall bin arch .
  (PBi.KnownBinary bin, MM.ArchConstraints arch) =>
  PB.ConcreteBlock arch bin ->
  ParsedFunctionMap arch bin ->
  IO Bool
isFunctionStart blk pfm = parsedFunctionContaining blk pfm >>= \case
  Just (Some dfi) -> do
    let baddr = PA.addrToMemAddr (PB.concreteAddress blk)
    return $ baddr == (MM.segoffAddr (MD.discoveredFunAddr dfi))
  Nothing -> return False

-- | Find the 'MD.ParsedBlock' corresponding to the entry of a function.
parsedBlockEntry ::
  forall bin arch .
  (PBi.KnownBinary bin, MM.ArchConstraints arch) =>
  PB.ConcreteBlock arch bin ->
  ParsedFunctionMap arch bin ->
  IO (Either String (Some (MD.ParsedBlock arch)))
parsedBlockEntry blk pfm = parsedFunctionContaining blk pfm >>= \case
  Just (Some dfi) -> do
    st <- IORef.readIORef (parsedStateRef pfm)
    let ds1 = discoveryState st
    let mem = MD.memory ds1
    case MM.resolveRegionOff mem (MM.addrBase baddr) (MM.addrOffset baddr) of
      Nothing -> return $ Left $ "Could not resolve address: " ++ show baddr
      Just faddr -> case Map.lookup faddr (dfi ^. MD.parsedBlocks) of
        Just pb -> return $ Right (Some pb)
        Nothing -> do
          let blkAddrs = Map.keys (dfi ^. MD.parsedBlocks)
          return $ Left $ ("Block not found in parsed blocks:\n" ++ show blkAddrs)
  Nothing -> return $ Left $ "No functions contain this block"
  where
    baddr = PA.addrToMemAddr (PB.concreteAddress blk)
