{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | Functionality for implementing on-demand code discovery in the InlineCallee feature
--
-- This enables code discovery when new instruction pointer values are
-- identified during symbolic execution, as well as dispatch to overrides
module Pate.Verification.DemandDiscovery (
    lookupFunction
  , toCrucibleCFG
  ) where

import           Control.Lens ( (&), (%~), (^.) )
import qualified Control.Lens as L
import qualified Data.BitVector.Sized as BVS
import qualified Data.Map as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import           Data.String ( fromString )
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Lang.Crucible.Analysis.Postdom as LCAP
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Core as CCC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Simulator.OverrideSim as LCSO
import qualified Lang.Crucible.Types as LCT
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WP

import qualified Pate.Address as PAd
import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Memory as PM
import qualified Pate.Monad.Context as PMC
import qualified Pate.Panic as PP
import qualified Pate.SymbolTable as PSym
import qualified Pate.Verification.Override as PVO

-- | A convenient Lens-styled combinator for updating a 'LCSO.FnBinding'
insertFnBinding
  :: LCSO.FnBinding p sym ext
  -> LCS.FunctionBindings p sym ext
  -> LCS.FunctionBindings p sym ext
insertFnBinding (LCS.FnBinding h s) m =
  LCS.FnBindings (CFH.insertHandleMap h s (LCS.fnBindings m))

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

-- | Call an override (specified as a pate 'PVO.Override') at this call site
--
-- This wrapper suitably transforms from machine arguments (i.e., the register
-- file representation) to logical C-like arguments, calls the override, and
-- then updates the machine state as-needed.
--
-- Like 'decodeAndCallFunction', this returns the function handle corresponding
-- to this override (newly-allocated) and updates the crucible state with the
-- appropriate mapping from handle to override.
callOverride
  :: forall arch sym p r f a ret args
   . (LCB.IsSymInterface sym)
  => LCS.SimState p sym (DMS.MacawExt arch) r f a
  -- ^ The crucible state at the call site
  -> LCT.TypeRepr (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
  -- ^ The type of the register file
  -> PVO.ArgumentMapping arch
  -- ^ The schema for converting from machine registers to structured argument lists
  -> PVO.Override sym args (DMS.MacawExt arch) ret
  -- ^ The override to arrange to be called from this call site
  -> IO ( CFH.FnHandle (LCT.EmptyCtx LCT.::> LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
                       (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
        , LCS.SimState p sym (DMS.MacawExt arch) r f a
        )
callOverride crucState regsRepr argMap ov = do
  let sym = crucState ^. LCS.stateContext . LCS.ctxSymInterface
  let halloc = crucState ^. LCS.stateContext . L.to LCS.simHandleAllocator
  hdl <- CFH.mkHandle' halloc (PVO.functionName ov) (Ctx.singleton regsRepr) regsRepr

  -- Create a wrapper override that extracts actual arguments (in a C-like
  -- argument list) from the raw machine state, which is represented as a
  -- register file. This also extracts the return value and suitably updates the
  -- register state when the override returns.
  let wrappedOverride = LCS.mkOverride' (PVO.functionName ov) regsRepr $ do
        initialMachineArgs <- LCS.getOverrideArgs
        let registerFile = LCS.regMap initialMachineArgs ^. Ctx.field @0
        let projectedActuals = PVO.functionIntegerArgumentRegisters argMap (PVO.functionArgsRepr ov) (LCS.regValue registerFile)
        let theOverride = PVO.functionOverride ov sym projectedActuals
        PVO.functionReturnRegister argMap (PVO.functionRetRepr ov) theOverride (LCS.regValue registerFile)

  let fnState = LCS.UseOverride wrappedOverride
  let fnBinding = LCS.FnBinding hdl fnState
  let crucState' = crucState & LCS.stateContext . LCS.functionBindings %~ insertFnBinding fnBinding
  return (hdl, crucState')

-- | Decode a function from the binary at the given 'BVS.BV' address using
-- macaw, translate it into a Crucible CFG, and bind it to a fresh function
-- handle that is ultimately used in 'lookupFunction'.
--
-- The return value is 1. the fresh function handle, and 2. the updated crucible
-- state with that handle bound to an appropriate CFG.
--
-- This is a key component of the incremental code discovery (and is the default
-- case if we do not have an override for the function)
decodeAndCallFunction
  :: forall sym arch bin mem binFmt p r f a
   . ( PA.ValidArch arch
     , LCB.IsSymInterface sym
     , PBi.KnownBinary bin
     )
  => PMC.ParsedFunctionMap arch bin
  -> DMS.GenArchVals mem arch
  -> MBL.LoadedBinary arch binFmt
  -> LCS.SimState p sym (DMS.MacawExt arch) r f a
  -- ^ The current crucible state while handling a macaw 'LookupFunctionHandle'
  -> LCT.TypeRepr (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
  -- ^ The type of the machine register file
  -> BVS.BV (DMC.ArchAddrWidth arch)
  -- ^ The instruction pointer to decode a function for
  -> IO ( CFH.FnHandle (LCT.EmptyCtx LCT.::> LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
                       (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
        , LCS.SimState p sym (DMS.MacawExt arch) r f a
        )
decodeAndCallFunction pfm archVals loadedBinary crucState regsRepr bvAddr =
  case concreteBlockFromBVAddr (Proxy @arch) PC.knownRepr (MBL.memoryImage loadedBinary) bvAddr of
    -- FIXME: This should probably be an exception, rather than a panic
    --
    -- It is plausible that a user could feed us a binary that triggered
    -- this (it would be a very strange and probably bad binary, but still
    -- externally triggerable)
    Left err -> PP.panic PP.InlineCallee "decodeAndCallFunction" ["Error while interpreting instruction pointer: " ++ show err]
    Right blk -> do
      -- FIXME: Here we are decoding the function at the given address in our
      -- binary. We need to also take in a symbol table to let us identify
      -- external calls (or calls to named functions) that we might have
      -- overrides for.
      mdfi <- PMC.parsedFunctionContaining blk pfm
      case mdfi of
        -- FIXME: This probably shouldn't be a panic - rather an exception, or perhaps an uninterpreted effect
        Nothing -> PP.panic PP.InlineCallee "lookupFunction" ["Unable to find mapping for address " ++ show bvAddr]
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
  => PVO.ArgumentMapping arch
  -> Map.Map PSym.Symbol (PVO.SomeOverride arch sym)
  -> PSym.SymbolTable arch
  -> PMC.ParsedFunctionMap arch bin
  -> DMS.GenArchVals mem arch
  -> MBL.LoadedBinary arch binFmt
  -> DMS.LookupFunctionHandle sym arch
lookupFunction argMap overrides symtab pfm archVals loadedBinary = DMS.LookupFunctionHandle $ \crucState _mem0 regs -> do
  let sym = crucState ^. LCS.stateContext . LCS.ctxSymInterface
  let regsRepr = LCT.StructRepr (DMS.crucArchRegTypes (DMS.archFunctions archVals))
  let regsEntry = LCS.RegEntry regsRepr regs
  let ipPtr = DMS.lookupReg archVals regsEntry DMC.ip_reg
  ipBV <- LCLM.projectLLVM_bv sym (LCS.regValue ipPtr)
  case WI.asBV ipBV of
    Nothing -> PP.panic PP.InlineCallee "lookupFunction" ["Non-constant target IP for call: " ++ show (WI.printSymExpr ipBV)]
    Just bv
      | Just calleeSymbol <- PSym.lookupSymbol bv symtab
      , Just (PVO.SomeOverride ov) <- Map.lookup calleeSymbol overrides ->
        callOverride crucState regsRepr argMap ov
      | otherwise -> decodeAndCallFunction pfm archVals loadedBinary crucState regsRepr bv
