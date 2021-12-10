{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Pate.Verification.InlineCallee ( inlineCallee ) where

import qualified Control.Lens as L
import qualified Control.Monad.Catch as CMC
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.BitVector.Sized as BVS
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import           Data.String ( fromString )
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import           GHC.Stack ( HasCallStack )
import           GHC.TypeLits ( type (<=) )

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Discovery as DMD
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Types as DMT
import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.CFG.Core as CCC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.DataLayout as LCLD
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as LCS
import qualified Lang.Crucible.Types as LCT
import qualified What4.BaseTypes as WT
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WP
import qualified What4.Symbol as WS

import qualified Pate.Abort as PAb
import qualified Pate.Address as PAd
import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import           Pate.Equivalence as PEq
import qualified Pate.Equivalence.Error as PEE
import           Pate.Monad
import qualified Pate.Monad.Context as PMC
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PF
import qualified Pate.Proof.Operations as PFO


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
  :: DMD.DiscoveryFunInfo arch ids
  -> EquivM sym arch (CCC.SomeCFG (DMS.MacawExt arch)
                                  (Ctx.EmptyCtx Ctx.::> LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch)))
                                  (LCT.StructType (DMS.CtxToCrucibleType (DMS.ArchRegContext arch))))
toCrucibleCFG dfi = do
  archFns <- L.view (L.to envArchVals . L.to DMS.archFunctions)
  halloc <- liftIO $ CFH.newHandleAllocator
  let fnName = discoveryFunName dfi
  let posFn = WP.OtherPos . fromString . show
  liftIO $ DMS.mkFunCFG archFns halloc fnName posFn dfi

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

stackSizeBytes :: Integer
stackSizeBytes = 1024 * 2

stackInitialOffset :: Integer
stackInitialOffset = 1024

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

symbolicallyExecute
  :: forall arch sym ids
   . DMD.DiscoveryFunInfo arch ids
  -> EquivM sym arch ()
symbolicallyExecute dfi = withSym $ \sym -> do
  CCC.SomeCFG cfg <- toCrucibleCFG dfi

  symArchFns <- L.view (L.to envArchVals . L.to DMS.archFunctions)
  let crucRegTypes = DMS.crucArchRegTypes symArchFns
  let regsRepr = LCT.StructRepr crucRegTypes

  let mem0 = undefined

  (mem1, sp) <- liftIO $ allocateStack (Proxy @arch) sym mem0
  initialRegisters <- liftIO $ DMS.macawAssignToCrucM (mkInitialRegVal symArchFns sym sp) (DMS.crucGenRegAssignment symArchFns)
  let initialRegsEntry = LCS.RegEntry regsRepr initialRegisters


  undefined initialRegsEntry

-- | Look up the macaw CFG for the given function address
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
  :: (HasCallStack)
  => StatePredSpec sym arch
  -> PPa.BlockPair arch
  -> EquivM sym arch (StatePredSpec sym arch, PFO.LazyProof sym arch PF.ProofBlockSliceType)
inlineCallee contPre pPair = do
  -- Normally we would like to treat errors leniently and continue on in a degraded state
  --
  -- However, if the user has specifically asked for two functions to be equated
  -- and we can't find them, we will just call that a fail-stop error (i.e.,
  -- 'functionFor' can throw an exception).
  Some oDFI <- functionFor @PBi.Original (PPa.pOriginal pPair)
  Some pDFI <- functionFor @PBi.Patched (PPa.pPatched pPair)

  symbolicallyExecute oDFI
  symbolicallyExecute pDFI

  let prfNode = PF.ProofInlinedCall { PF.prfInlinedCallees = pPair
                                    }
  lproof <- PFO.lazyProofApp prfNode
  return (undefined, lproof)
