{-|
Module           : Pate.CounterExample
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Representation and presentation of the equivalence proofs
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE DeriveTraversable   #-}

module Pate.Proof
  ( EquivTripleBody(..)
  , EquivTriple
  --, SomeProof(..)
  --, VerificationStatus(..)
  --, ProofBlockSliceBody(..)
  , ProofBlockSlice
  , ProofFunctionCall(..)
  --, SomeProofTriple(..)
  --, trivialSliceBody
  --, prfPre
  --, prfBodyPre
  , IsBoolLike(..)
  , type ProofBlockType
  , type ProofRegisterType
  , type ProofPredicateType
  , type ProofMemoryCellType
  , type ProofMemoryPolarityType
  , type ProofStatusType
  , type ProofContextType
  ) where

import           GHC.Natural
--import           GHC.Type
--import qualified Data.Aeson as AS
import           Control.Applicative

import qualified Data.Map as Map
import           Data.List
import           Data.Functor.Identity

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import           Data.Parameterized.TH.GADT
import           Data.Proxy
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as TFC

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Simulator.RegValue as CS

import qualified Pate.Types as PT
import qualified Pate.Equivalence as PE
import qualified Pate.MemCell as PMC
import qualified Pate.Memory.MemTrace as PMT
import qualified Pate.SimState as PS
import qualified Pate.SimulatorRegisters as PSR
import qualified Pate.ExprMappable as PEM

import qualified Pate.Parallel as Par
import qualified What4.Interface as W4

---------------------------------------------
-- proof objects



-- | The body of an 'EquivTriple'.
data EquivTripleBody sym arch where
  EquivTripleBody ::
    {
      eqPair :: PT.BlockPair arch
      -- ^ the entry points that yield equivalent states on the post-domain
      -- after execution, assuming initially equivalent states on the pre-domain
    , eqPreDomain :: PE.StatePred sym arch
      -- ^ the pre-domain: the state that was assumed initially equivalent
      -- closed over the bound variables representing the initial state
    , eqPostDomain :: PE.StatePredSpec sym arch
      -- ^ the post-domain: the state that was proven equivalent after execution
      -- abstracted over the bound variables representing the final state
    , eqValidSym :: PT.Sym sym
    } -> EquivTripleBody sym arch

instance PEM.ExprMappable sym (EquivTripleBody sym arch) where
  mapExpr sym f triple = do
    eqPreDomain' <- PEM.mapExpr sym f (eqPreDomain triple)
    eqPostDomain' <- PEM.mapExpr sym f (eqPostDomain triple)
    return $ EquivTripleBody (eqPair triple) eqPreDomain' eqPostDomain' (eqValidSym triple)

-- | An triple representing the equivalence conditions for a block pair. Abstracted
-- over the initial machine state.
type EquivTriple sym arch = PS.SimSpec sym arch (EquivTripleBody sym arch)

-- data ProofFunctionCall' sym arch =
--     ProofFunctionCall'
--       {
--         -- | proof that the correct pre-domain is established equivalent
--         -- prior to the function call
--         prfFunPre :: EquivTripleBody sym arch
--         -- | proof that the function itself establishes equivalence on the target
--         -- post-domain. Note that it is a 'ProofBlockSlice' since we do not need to
--         -- bind the initial machine state that was in scope for this call.
--       , prfFunBody :: ProofBlockSlice' sym arch
--         -- | proof that the target post-domain following the function call
--         -- establishes the overall target post-domain equivalence. Again this does not
--         -- bind the initial state.
--       , prfFunCont :: ProofBlockSlice' sym arch
--       }
--   | ProofTailCall
--       { prfFunPre :: EquivTripleBody sym arch
--       , prfFunBody :: ProofBlockSlice' sym arch
--       } 

-- instance PEM.ExprMappable sym (ProofFunctionCall' sym arch) where
--   mapExpr sym f prf = do
--     prfFunPre' <- PEM.mapExpr sym f (prfFunPre prf)
--     prfFunCont' <- PEM.mapExpr sym f (prfFunCont prf)
--     case prf of
--       ProofFunctionCall'{} -> do
--         prfFunBody' <- PEM.mapExpr sym f (prfFunBody prf)
--         return $ ProofFunctionCall' prfFunPre' prfFunBody' prfFunCont'
--       ProofTailCall{} -> return $ ProofTailCall prfFunPre' prfFunCont'

-- -- | Trace of the proof that a pair of block "slices" satisfy the
-- -- given triple. 
-- data ProofBlockSliceBody sym arch =
--   ProofBlockSliceBody
--       { -- | the top-level triple for this slice, stating that
--         -- all possible exits satisfy equivalence on the post-domain
--         -- given equivalence on the pre-domain
--         prfTriple :: EquivTripleBody sym arch
--         -- | all jumps which exit the slice with a function call
--       , prfFunCalls :: [ProofFunctionCall' sym arch]
--       , prfReturn :: Maybe (EquivTripleBody sym arch)
--       , prfUnknownExit :: Maybe (EquivTripleBody sym arch)
--       }

-- instance PEM.ExprMappable sym (ProofBlockSliceBody sym arch) where
--   mapExpr sym f prf = do
--     prfTriple' <- PEM.mapExpr sym f (prfTriple prf)
--     prfFunCalls' <- mapM (PEM.mapExpr sym f) (prfFunCalls prf)
--     prfReturn' <- mapM (PEM.mapExpr sym f) (prfReturn prf)
--     prfUnknownExit' <- mapM (PEM.mapExpr sym f) (prfUnknownExit prf)
--     return $ ProofBlockSliceBody prfTriple' prfFunCalls' prfReturn' prfUnknownExit'


-- trivialSliceBody :: EquivTripleBody sym arch -> ProofBlockSliceBody sym arch
-- trivialSliceBody triple = ProofBlockSliceBody triple [] Nothing Nothing

-- prfBodyPre :: ProofBlockSliceBody sym arch -> PE.StatePred sym arch
-- prfBodyPre = eqPreDomain . prfTriple

-- -- | A trace for the proof of a given triple, abstracted over an initial machine state.
-- type ProofBlockSlice' sym arch = PS.SimSpec sym arch (ProofBlockSliceBody sym arch)

-- prfPre :: ProofBlockSlice' sym arch -> PE.StatePredSpec sym arch
-- prfPre = PS.specMap prfBodyPre

-- -- | 'EquivTriple' abstracted over the specific expression builder. Used for reporting.
-- data SomeProofBlockSlice arch where
--   SomeProofBlockSlice ::
--     PT.Sym sym -> ProofBlockSlice' sym arch -> SomeProofBlockSlice arch
-- instance PT.ValidArch arch => Show (SomeProofBlockSlice arch) where
--   show (SomeProofBlockSlice vsym prf) = show (ppProofBlockSlice vsym prf)


-- data SomeProofGoal arch where
--   SomeProofGoal ::
--     PT.ValidArch arch =>
--     PT.Sym sym ->
--     EquivTriple sym arch ->
--     ProofBlockSlice' sym arch ->
--     SomeProofGoal arch
-- instance Show (SomeProofGoal arch) where
--   show (SomeProofGoal vsym triple prf) = show (ppProofGoal vsym triple prf)



-- data ConcreteBlockJson =
--   ConcreteBlockJson
--     {
--       jsBlockAddr :: Word64
--     }

-- data AddressJson =
--   AddressJson
--     {
--       jsAddrText :: T.Text
--     }

-- data RegJson = RegJson { jsRegName :: T.Text }

-- data PredJson = PredJson { jsPred :: Maybe Bool }

-- data RegDomainJson = RegDomainJson { jsRegDomain :: [(RegJSon, PredJson)] }

-- data MemCellJson = MemCellJson
--   { jsMemCellAddr :: AddressJson
--   , jsMemCellSize :: Int
--   }

-- data MemDomainJson = MemDomainJson
--   { jsMemPolarity :: PredJson, jsMemDomain :: [(MemCellJson, PredJson)] }


-- data CounterExampleJson =

-- data VerificationStatusJson =
--     UnverifiedJson
--   | VerificationSkippedJson
--   | VerificationSuccessJson
--   | VerificationFailJson 

-- data EquivTripleJson where
--   EquivTripleJson ::
--     {
--       jsEqOriginalAddr :: ConcreteBlockJson
--     , jsEqPatchedAddr :: ConcreteBlockJson
--     , eqPostDomain :: PE.StatePredSpec sym arch
--       -- ^ the post-domain: the state that was proven equivalent after execution
--       -- abstracted over the bound variables representing the final state
--     , eqStatus :: Par.Future (VerificationStatus arch)
--       -- ^ flag indicating whether or not this triple has passed verification
--     , eqValidSym :: PT.Sym sym
--     } -> EquivTripleBody sym arch

-- data ProofBlockSliceJson  =
--   ProofBlockSliceJson
--       { -- | the top-level triple for this slice, stating that
--         -- all possible exits satisfy equivalence on the post-domain
--         -- given equivalence on the pre-domain
--         prfTriple :: EquivTripleBody sym arch
--         -- | all jumps which exit the slice with a function call
--       , prfFunCalls :: [ProofFunctionCall sym arch]
--       , prfReturn :: Maybe (EquivTripleBody sym arch)
--       , prfUnknownExit :: Maybe (EquivTripleBody sym arch)
--       }

----------------------------------------------
-- printing

data ProofAnn

type ProofDoc = PP.Doc ProofAnn

ppMaybe :: Maybe f -> (f ->  PP.Doc a) -> PP.Doc a
ppMaybe (Just f) pp = pp f
ppMaybe Nothing _ = PP.emptyDoc

-- ppProofGoal ::
--   PrettyProof e =>
--   ProofTriple e ->
--   ProofBlockSlice e ->
--   ProofDoc
-- ppProofGoal triple prf =
--   PP.vsep
--     [ "Top-level equivalence goal: "
--     --, ppBlockPairReturn (eqPair $ PS.specBody triple)
--     --, PP.indent 2 $ ppEquivTriple vsym triple
--     , "Equivalence proof:"
--     --, PP.indent 2 $ ppProofBlockSlice vsym prf
--     ]

-- ppProofBlockSlice ::
--   PT.ValidArch arch =>
--   PT.Sym sym ->
--   ProofBlockSlice' sym arch ->
--   ProofDoc
-- ppProofBlockSlice vsym prf =
--   PP.vsep
--     [ ppEquivTriple vsym (PS.specMap prfTriple prf)
--     , "Proof:"
--     , PP.indent 4 $ 
--         (case funCalls of
--           [] -> PP.emptyDoc
--           _ -> "Function Calls: "
--                <> PP.line
--                <> PP.indent 4 (PP.vsep (map (ppProofFunctionCallSpec vsym . PS.attachSpec prf) funCalls))
--                <> PP.line
--         )
--         <> (ppMaybe (prfReturn prfBody) $ \trip ->
--           PP.vsep
--             [ "Function Return: "
--             , PP.indent 4 $ ppEquivTriple vsym (PS.attachSpec prf trip)
--             ])
--         <> (ppMaybe (prfUnknownExit prfBody) $ \trip ->
--           PP.vsep
--             [ "Unknown function exit: "
--             , PP.indent 4 $ ppEquivTriple vsym (PS.attachSpec prf trip)
--             ])
--     ]
--   where
--     funCalls = prfFunCalls prfBody
--     prfBody = PS.specBody prf

-- -- we need to plumb through the initial variables, since they
-- -- are used when describing the triple that proves this function call
-- -- is valid
-- ppProofFunctionCallSpec ::
--   PT.ValidArch arch =>
--   PT.Sym sym ->
--   PS.SimSpec sym arch (ProofFunctionCall' sym arch) ->
--   ProofDoc
-- ppProofFunctionCallSpec vsym prfCallSpec =
--   PP.vsep $ 
--     [ "Function pre-domain is satisfied before call:"
--     , PP.indent 4 $ ppBlockPairTarget startPair funPair
--     , PP.indent 4 $ ppEquivTriple vsym prfPreTriple
--     , "Function satisfies post-domain upon return:"
--     , PP.indent 4 $ ppBlockPairReturn funPair
--     , PP.indent 4 $ ppProofBlockSlice vsym $ prfFunBody prfCall
--     ] ++ case prfCall of
--       ProofFunctionCall'{} ->
--         [ "Continuing after function return satisfies post-domain for caller."
--         , PP.indent 4 $ ppBlockPairReturn contPair
--         , PP.indent 4 $ ppProofBlockSlice vsym $ prfFunCont prfCall
--         ]
--       ProofTailCall{} -> []
--   where
--     startPair = eqPair $ PS.specBody prfPreTriple
--     funPair = eqPair $ prfTriple $ PS.specBody $ prfFunBody prfCall
--     contPair = eqPair $ prfTriple $ PS.specBody $ prfFunCont prfCall

--     prfPreTriple = PS.specMap prfFunPre prfCallSpec
--     prfCall = PS.specBody prfCallSpec



-- ppEquivTriple :: PT.ValidArch arch => PT.Sym sym -> EquivTriple sym arch -> ProofDoc
-- ppEquivTriple vsym triple =
--   PP.vsep
--     [ "Pre-domain:"
--     , PP.indent 4 $ ppStatePredSpec vsym (PS.specMap eqPreDomain triple)
--     , "Post-domain:"
--     , PP.indent 4 $ ppStatePredSpec vsym (eqPostDomain tripleBody)
--     ]
--   where
--     tripleBody = PS.specBody triple

-- ppStatePredSpec ::
--   forall sym arch.
--   PT.ValidArch arch =>
--   PT.Sym sym ->
--   PE.StatePredSpec sym arch ->
--   ProofDoc
-- ppStatePredSpec vsym@(PT.Sym _ _) stpred =
--   ppRegs <> ppStack <> ppMem
--     where
--       stPredBody = PS.specBody stpred

--       ppReg :: (Some (MM.ArchReg arch), W4.Pred sym) -> ProofDoc
--       ppReg (Some reg, p) = case W4.asConstantPred p of
--         Just False -> PP.emptyDoc
--         Just True -> PP.pretty $ showF reg
--         _ -> PP.pretty (showF reg) <> PP.line <> PP.indent 1 "Conditional"
      
--       ppRegs :: ProofDoc
--       ppRegs = case Map.toList (PE.predRegs stPredBody) of
--         [] -> PP.emptyDoc
--         regs | length regs == length (MM.archRegs @(MM.ArchReg arch)) -> "All Registers" <> PP.line
--         regs -> "Registers: " <> PP.line <> PP.indent 2 (PP.vsep (map ppReg regs)) <> PP.line

--       ppCell :: forall w. PMC.MemCell sym arch w -> W4.Pred sym -> ProofDoc
--       ppCell cell p = case W4.asConstantPred p of
--         Just False -> PP.emptyDoc
--         Just True -> cellpp
--         _ -> cellpp <> PP.line <> PP.indent 1 "Conditional"
--         where
--           cellpp =
--             let CLM.LLVMPointer reg off = PMC.cellPtr cell
--             in ppExpr vsym reg <> "+" <> ppBV off

--       ppMemPred :: PE.MemPred sym arch -> (Maybe ProofDoc, Maybe Bool)
--       ppMemPred mempred = case cells of
--         [] -> (Nothing, polarity)
--         _ -> (Just $ PP.indent 2 (PP.vsep ppCells), polarity)
--         where
--           cells = PE.memPredToList mempred
--           polarity = W4.asConstantPred (PE.memPredPolarity mempred)

--           ppCells = map (\(Some cell, p) -> ppCell cell p) cells

--       ppPolarity :: Maybe Bool -> ProofDoc
--       ppPolarity pol = case pol of
--         Just True -> PP.parens "inclusive"
--         Just False -> PP.parens "exclusive"
--         _ -> PP.parens "symbolic polarity"

--       ppStack :: ProofDoc
--       ppStack = case ppMemPred (PE.predStack stPredBody) of
--         (Just stack, pol) -> "Stack:" <+> ppPolarity pol <> PP.line <> stack <> PP.line
--         (Nothing, Just False) -> "All Stack Memory" <> PP.line
--         (Nothing, _) -> PP.emptyDoc

--       ppMem :: ProofDoc
--       ppMem = case ppMemPred (PE.predMem stPredBody) of
--         (Just global, pol) -> "Global Memory:" <+> ppPolarity pol <> PP.line <> global <> PP.line
--         (Nothing, Just False) -> "All Global Memory" <> PP.line
--         (Nothing, _) -> PP.emptyDoc

--       ppBV :: W4.SymBV sym w -> ProofDoc
--       ppBV e = PP.pretty $ showF e

-- ppExpr :: PT.Sym sym -> W4.SymExpr sym tp -> ProofDoc
-- ppExpr (PT.Sym _ _) e = PP.pretty $ showF e

-- ppBlockPair :: PT.ValidArch arch => PT.BlockPair arch -> ProofDoc
-- ppBlockPair pPair =
--   PP.hsep
--     [ "Original:" 
--     , PP.pretty $ PT.ppBlock (PT.pOriginal pPair)
--     , "vs."
--     , "Patched:"
--     , PP.pretty $ PT.ppBlock (PT.pPatched pPair)
--     ]

-- ppBlockPairReturn :: PT.ValidArch arch => PT.BlockPair arch -> ProofDoc
-- ppBlockPairReturn pPair =
--   PP.hsep
--     [ PP.parens (PP.pretty (PT.ppBlock (PT.pOriginal pPair)) <+> "-> return")
--     , "vs."
--     , PP.parens (PP.pretty (PT.ppBlock (PT.pPatched pPair)) <+> "-> return")
--     ]

-- ppBlockPairTarget :: PT.ValidArch arch => PT.BlockPair arch -> PT.BlockPair arch -> ProofDoc
-- ppBlockPairTarget srcPair tgtPir =
--   PP.hsep
--     [ PP.parens (PP.pretty (PT.ppBlock (PT.pOriginal srcPair)) <+> "->" <+> PP.pretty (PT.ppBlock (PT.pOriginal tgtPir)))
--     , "vs."
--     , PP.parens (PP.pretty (PT.ppBlock (PT.pPatched srcPair)) <+> "->" <+> PP.pretty (PT.ppBlock (PT.pPatched tgtPir)))
--     ]


----------------------------------------------
-- Serialization

data ProofElemType =
    ProofBlockType
  | ProofRegisterType
  | ProofPredicateType
  | ProofMemoryCellType
  | ProofMemoryPolarityType
  | ProofStatusType
  | ProofContextType


type ProofBlockType = 'ProofBlockType
type ProofRegisterType = 'ProofRegisterType
type ProofPredicateType = 'ProofPredicateType
type ProofMemoryCellType = 'ProofMemoryCellType
type ProofMemoryPolarityType = 'ProofMemoryPolarityType
type ProofStatusType = 'ProofStatusType
type ProofContextType = 'ProofContextType

-- | Proof that the top-level triple is satisfied, according to all possible
-- exits from the given block slice
data ProofBlockSlice (e :: ProofElemType -> *) =
  ProofBlockSlice
    { prfBlockSliceTriple :: ProofTriple e
    , prfBlockSliceCalls :: [ProofFunctionCall e]
    , prfBlockSliceReturn :: Maybe (ProofTriple e)
    , prfBlockSliceUnknownExit :: Maybe (ProofTriple e)
    }

instance TF.FunctorF ProofBlockSlice where
  fmapF = TF.fmapFDefault

instance TF.FoldableF ProofBlockSlice where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF ProofBlockSlice where
  traverseF f (ProofBlockSlice a1 a2 a3 a4) =
    ProofBlockSlice
      <$> TF.traverseF f a1
      <*> traverse (TF.traverseF f) a2
      <*> traverse (TF.traverseF f) a3
      <*> traverse (TF.traverseF f) a4

instance PrettyProofElem e => PP.Pretty (ProofBlockSlice e) where
  pretty prf = 
   PP.vsep
     [ PP.pretty (prfBlockSliceTriple prf)
     , "Proof:"
     , PP.indent 4 $ 
         (case prfBlockSliceCalls prf of
           [] -> PP.emptyDoc
           funCalls -> "Function Calls: "
                <> PP.line
                <> PP.indent 4 (PP.vsep (map PP.pretty funCalls))
                <> PP.line
         )
         <> (ppMaybe (prfBlockSliceReturn prf) $ \trip ->
           PP.vsep
             [ "Function Return: "
             , PP.indent 4 $ PP.pretty trip
             ])
         <> (ppMaybe (prfBlockSliceUnknownExit prf) $ \trip ->
           PP.vsep
             [ "Unknown function exit: "
             , PP.indent 4 $ PP.pretty trip
             ])
     ]

-- | Proof that a function call is valid
data ProofFunctionCall (e :: ProofElemType -> *) =
  ProofFunctionCall
    { prfFunctionCallPre :: ProofTriple e
    , prfFunctionCallBody :: ProofBlockSlice e
    , prfFunctionCallContinue :: Maybe (ProofBlockSlice e)
    }

instance TF.FunctorF ProofFunctionCall where
  fmapF = TF.fmapFDefault

instance TF.FoldableF ProofFunctionCall where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF ProofFunctionCall where
  traverseF f (ProofFunctionCall a1 a2 a3) =
    ProofFunctionCall
      <$> TF.traverseF f a1
      <*> TF.traverseF f a2
      <*> traverse (TF.traverseF f) a3

instance PrettyProofElem e => PP.Pretty (ProofFunctionCall e) where
 pretty prf =
   PP.vsep $ 
     [ "Function pre-domain is satisfied before call:"
     , PP.indent 4 $ ppBlockPairTarget (prfTripleBlocks $ prfFunctionCallPre prf) (prfTripleBlocks $ prfBlockSliceTriple $ prfFunctionCallBody prf)
     , PP.indent 4 $ PP.pretty $ prfFunctionCallPre prf
     , "Function satisfies post-domain upon return:"
     , PP.indent 4 $ PP.pretty $ prfFunctionCallBody prf
     ] ++ case prfFunctionCallContinue prf of
       Just cont ->
         [ "Continuing after function return satisfies post-domain for caller."
         , PP.indent 4 $ ppBlockPairReturn (prfTripleBlocks $ prfBlockSliceTriple cont)
         ]
       Nothing -> []
   where
     ppBlockPairReturn :: PT.PatchPairC (e 'ProofBlockType) -> PP.Doc a
     ppBlockPairReturn pPair = PT.ppPatchPairCEq go pPair
       where
         go :: e 'ProofBlockType -> PP.Doc a
         go blk = PP.parens (PP.pretty blk <+> "-> return")

     ppBlockPairTarget :: PT.PatchPairC (e 'ProofBlockType) -> PT.PatchPairC (e 'ProofBlockType) -> PP.Doc a
     ppBlockPairTarget srcPair tgtPair =
       PT.ppPatchPairCEq go (PT.mergePatchPairCs srcPair tgtPair)
       where
         go :: (e 'ProofBlockType, e 'ProofBlockType) -> PP.Doc a
         go (src, tgt) = PP.parens (PP.pretty src) <+> "->" <+> PP.pretty tgt

data ProofRegisterDomain (e :: ProofElemType -> *) =
  ProofRegisterDomain
    { prfRegisterDomain :: [(e 'ProofRegisterType, e 'ProofPredicateType)] }

instance TF.FunctorF ProofRegisterDomain where
  fmapF = TF.fmapFDefault

instance TF.FoldableF ProofRegisterDomain where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF ProofRegisterDomain where
  traverseF f (ProofRegisterDomain a1) =
    ProofRegisterDomain <$> traverse (\(a, b) -> (,) <$> f a <*> f b) a1

instance PrettyProofElem e => PP.Pretty (ProofRegisterDomain e) where
  pretty prf = PP.vsep (map ppReg (prfRegisterDomain prf))
    where
      ppReg :: (e 'ProofRegisterType, e 'ProofPredicateType) -> PP.Doc a
      ppReg (reg, p) = case asBool p of
        Just False -> PP.emptyDoc
        Just True -> PP.pretty reg
        _ -> PP.pretty reg <> PP.line <> PP.indent 1 (PP.pretty p)


data ProofMemoryDomain (e :: ProofElemType -> *) =
  ProofMemoryDomain
    { prfMemoryDomain :: [(e 'ProofMemoryCellType, e 'ProofPredicateType)]
    , prfMemoryDomainPolarity :: e 'ProofMemoryPolarityType
    }

instance TF.FunctorF ProofMemoryDomain where
  fmapF = TF.fmapFDefault

instance TF.FoldableF ProofMemoryDomain where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF ProofMemoryDomain where
  traverseF f (ProofMemoryDomain a1 a2) =
    ProofMemoryDomain <$> traverse (\(a, b) -> (,) <$> f a <*> f b) a1 <*> f a2

instance PrettyProofElem e => PP.Pretty (ProofMemoryDomain e) where
  pretty prf =
    PP.pretty (prfMemoryDomainPolarity prf) <> PP.line <> PP.vsep (map ppMem (prfMemoryDomain prf))
    where
      ppMem :: (e 'ProofMemoryCellType, e 'ProofPredicateType) -> PP.Doc a
      ppMem (cell, p) = case asBool p of
        Just False -> PP.emptyDoc
        Just True -> PP.pretty cell
        _ -> PP.pretty cell <> PP.line <> PP.indent 1 (PP.pretty p)

data ProofDomain (e :: ProofElemType -> *) =
  ProofDomain
    { prfDomainRegisters :: ProofRegisterDomain e
    , prfDomainStackMemory :: ProofMemoryDomain e
    , prfDomainGlobalMemory :: ProofMemoryDomain e
    , prfDomainContext :: e 'ProofContextType
    }

instance TF.FunctorF ProofDomain where
  fmapF = TF.fmapFDefault

instance TF.FoldableF ProofDomain where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF ProofDomain where
  traverseF f (ProofDomain a1 a2 a3 a4) =
    ProofDomain
    <$> TF.traverseF f a1
    <*> TF.traverseF f a2
    <*> TF.traverseF f a3
    <*> f a4

instance PrettyProofElem e => PP.Pretty (ProofDomain e) where
  pretty prf = PP.vsep
    [ "Registers:"
    , PP.pretty (prfDomainRegisters prf)
    , "Stack Memory:"
    , PP.pretty (prfDomainStackMemory prf)
    , "Global Memory:"
    , PP.pretty (prfDomainGlobalMemory prf)
    ]
    

data ProofTriple (e :: ProofElemType -> *) =
  ProofTriple
    { prfTripleBlocks :: PT.PatchPairC (e 'ProofBlockType) 
    , prfTriplePreDomain :: ProofDomain e
    , prfTriplePostDomain :: ProofDomain e
    , prfTripleStatus :: e 'ProofStatusType
    }


instance TF.FunctorF ProofTriple where
  fmapF = TF.fmapFDefault

instance TF.FoldableF ProofTriple where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF ProofTriple where
  traverseF f (ProofTriple a1 a2 a3 a4) =
    ProofTriple
    <$> traverse f a1
    <*> TF.traverseF f a2
    <*> TF.traverseF f a3
    <*> f a4

instance PrettyProofElem e => PP.Pretty (ProofTriple e) where
 pretty prf =
   PP.vsep
     [ PT.ppPatchPairCEq PP.pretty (prfTripleBlocks prf)
     , "Pre-domain:"
     , PP.indent 4 $ PP.pretty (prfTriplePreDomain prf)
     , "Post-domain:"
     , PP.indent 4 $ PP.pretty (prfTriplePostDomain prf)
     , "Verification Status:"
     , PP.indent 4 $ PP.pretty (prfTripleStatus prf)
     ]

class (IsBoolLike (e 'ProofPredicateType),
       Eq (e 'ProofBlockType),
       (forall tp. PP.Pretty (e tp))) => PrettyProofElem e

class IsBoolLike tp where
  asBool :: tp -> Maybe Bool

-- Counterexample printing

-- ppEquivalenceError ::
--   EquivalenceError arch -> String
-- ppEquivalenceError err@(EquivalenceError{}) | (InequivalentError ineq)  <- errEquivError err =
--   ppInequivalenceResult ineq
-- ppEquivalenceError err = "-\n\t" ++ show err ++ "\n" -- TODO: pretty-print the error

-- ppReason :: InequivalenceReason -> String
-- ppReason r = "\tEquivalence Check Failed: " ++ case r of
--   InequivalentRegisters -> "Final registers diverge."
--   InequivalentMemory -> "Final memory states diverge."
--   InvalidCallPair -> "Unexpected next IPs."
--   InvalidPostState -> "Post state is invalid."
--   PostRelationUnsat -> "Post-equivalence relation cannot be satisifed"

-- ppExitCaseDiff :: ExitCaseDiff -> String
-- ppExitCaseDiff (eO, eP) | eO == eP = "\tBlock Exited with " ++ ppExitCase eO
-- ppExitCaseDiff (eO, eP) =
--   "\tBlocks have different exit conditions: "
--   ++ ppExitCase eO ++ " (original) vs. "
--   ++ ppExitCase eP ++ " (rewritten)"

ppExitCase :: MS.MacawBlockEndCase -> String
ppExitCase ec = case ec of
  MS.MacawBlockEndJump -> "arbitrary jump"
  MS.MacawBlockEndCall -> "function call"
  MS.MacawBlockEndReturn -> "function return"
  MS.MacawBlockEndBranch -> "branch"
  MS.MacawBlockEndArch -> "syscall"
  MS.MacawBlockEndFail -> "analysis failure"

-- ppMemTraceDiff :: MemTraceDiff arch -> String
-- ppMemTraceDiff diffs = "\tTrace of memory operations:\n" ++ concatMap ppMemOpDiff diffs

-- ppMemOpDiff :: MemOpDiff arch -> String
-- ppMemOpDiff diff
--   | shouldPrintMemOp diff
--   =  "\t\t" ++ ppDirectionVerb (mIsRead diff) ++ " "
--   ++ ppGroundMemOp (mIsRead diff) (mOpOriginal diff)
--   ++ (if mOpOriginal diff == mOpRewritten diff
--       then ""
--       else
--         " (original) vs. " ++ ppGroundMemOp (mIsRead diff) (mOpRewritten diff) ++ " (rewritten)"
--          ++ mDesc diff
--      )
--   ++ "\n"
-- ppMemOpDiff _ = ""

-- shouldPrintMemOp :: MemOpDiff arch -> Bool
-- shouldPrintMemOp diff =
--   mOpOriginal diff /= mOpRewritten diff ||
--   gCondition (mOpOriginal diff) ||
--   gCondition (mOpRewritten diff)

-- ppGroundMemOp :: Bool -> GroundMemOp arch -> String
-- ppGroundMemOp isRead op
--   | Some v <- gValue op
--   =  show v
--   ++ " " ++ ppDirectionPreposition isRead ++ " "
--   ++ ppLLVMPointer (gAddress op)
--   ++ if gCondition op
--      then ""
--      else " (skipped)"

-- ppDirectionVerb :: Bool -> String
-- ppDirectionVerb True = "read"
-- ppDirectionVerb False = "wrote"

-- ppDirectionPreposition :: Bool -> String
-- ppDirectionPreposition True = "from"
-- ppDirectionPreposition False = "to"

-- _ppEndianness :: MM.Endianness -> String
-- _ppEndianness MM.BigEndian = "→"
-- _ppEndianness MM.LittleEndian = "←"

-- ppPreRegs ::
--   HasCallStack =>
--   MM.RegState (MM.ArchReg arch) (RegisterDiff arch)
--   -> String
-- ppPreRegs diffs = "\tInitial registers of a counterexample:\n" ++ case TF.foldMapF ppPreReg diffs of
--   (Sum 0, s) -> s
--   (Sum n, s) -> s ++ "\t\t(and " ++ show n ++ " other all-zero slots)\n"

-- ppPreReg ::
--   HasCallStack =>
--   RegisterDiff arch tp ->
--   (Sum Int, String)
-- ppPreReg diff = case rTypeRepr diff of
--   CLM.LLVMPointerRepr _
--     | GroundBV _ obv <- rPreOriginal diff
--     , GroundBV _ pbv <- rPrePatched diff ->
--       case (BVS.asUnsigned obv, BVS.asUnsigned pbv) of
--         (0, 0) -> (1, "")
--         _ | obv == pbv -> (0, ppSlot diff ++ show (rPreOriginal diff) ++ "\n")
--         _ -> (0, ppSlot diff ++ show (rPreOriginal diff) ++ "(original) vs. " ++ show (rPrePatched diff) ++ "\n")
--   CLM.LLVMPointerRepr _ ->
--     case (rPreOriginal diff) == (rPrePatched diff) of
--       True -> (0, ppSlot diff ++ show (rPreOriginal diff)  ++ "\n")
--       False -> (0, ppSlot diff ++ show (rPreOriginal diff)  ++ "(original) vs. " ++ show (rPrePatched diff) ++ "\n")
--   CT.BoolRepr
--     | rPreOriginal diff == rPrePatched diff -> (0, ppSlot diff ++ show (rPreOriginal diff) ++ "\n")
--     | otherwise -> (0, ppSlot diff ++ show (rPreOriginal diff)  ++ "(original) vs. " ++ show (rPrePatched diff) ++ "\n")
--   CT.StructRepr Ctx.Empty -> (0, ppSlot diff ++ show (rPreOriginal diff) ++ "\n")
--   _ -> (0, ppSlot diff ++ "unsupported register type in precondition pretty-printer\n")

-- ppDiffs ::
--   MS.SymArchConstraints arch =>
--   MM.RegState (MM.ArchReg arch) (RegisterDiff arch) ->
--   String
-- ppDiffs diffs =
--   "\tFinal IPs: "
--   ++ show (rPostOriginal (diffs ^. MM.curIP))
--   ++ " (original) vs. "
--   ++ show (rPostPatched (diffs ^. MM.curIP))
--   ++ " (rewritten)\n"
--   ++ "\tMismatched resulting registers:\n" ++ TF.foldMapF ppDiff diffs

-- ppDiff ::
--   RegisterDiff arch tp ->
--   String
-- ppDiff diff | rPostEquivalent diff = ""
-- ppDiff diff = ppSlot diff ++ case rTypeRepr diff of
--   CLM.LLVMPointerRepr _ -> ""
--     ++ show (rPostOriginal diff)
--     ++ " (original) vs. "
--     ++ show (rPostPatched diff)
--     ++ " (rewritten)\n"
--     ++ rDiffDescription diff
--     ++ "\n\n"
--   _ -> "unsupported register type in postcondition comparison pretty-printer\n"

-- ppRegEntry :: SymGroundEvalFn sym -> PSR.MacawRegEntry sym tp -> IO String
-- ppRegEntry fn (PSR.MacawRegEntry repr v) = case repr of
--   CLM.LLVMPointerRepr _ | CLM.LLVMPointer _ offset <- v -> showModelForExpr fn offset
--   _ -> return "Unsupported register type"


-- showModelForPtr :: forall sym w.
--   SymGroundEvalFn sym ->
--   CLM.LLVMPtr sym w ->
--   IO String
-- showModelForPtr fn (CLM.LLVMPointer reg off) = do
--   regStr <- showModelForExpr fn reg
--   offStr <- showModelForExpr fn off
--   return $ "Region:\n" ++ regStr ++ "\n" ++ offStr

-- ppMemDiff ::
--   SymGroundEvalFn sym ->
--   CLM.LLVMPtr sym ptrW ->
--   CLM.LLVMPtr sym w ->
--   CLM.LLVMPtr sym w ->
--   IO String
-- ppMemDiff fn ptr val1 val2 = do
--   ptrStr <- showModelForPtr fn ptr
--   val1Str <- showModelForPtr fn val1
--   val2Str <- showModelForPtr fn val2
--   return $ "Pointer: " ++ ptrStr ++ "\nValue (original)" ++ val1Str ++ "\nValue (patched)" ++ val2Str

-- ppRegDiff ::
--   SymGroundEvalFn sym ->
--   PSR.MacawRegEntry sym tp ->
--   PSR.MacawRegEntry sym tp ->
--   IO String
-- ppRegDiff fn reg1 reg2 = do
--   origStr <- ppRegEntry fn reg1
--   patchedStr <- ppRegEntry fn reg2
--   return $ "Original: \n" ++ origStr ++ "\n\nPatched: \n" ++ patchedStr

-- ppSlot ::
--   RegisterDiff arch tp
--   -> String
-- ppSlot (RegisterDiff { rReg = reg })  = "\t\tslot " ++ (pad 4 . showF) reg ++ ": "

-- ppAbortedResult :: CS.AbortedResult sym ext -> String
-- ppAbortedResult (CS.AbortedExec reason _) = show reason
-- ppAbortedResult (CS.AbortedExit code) = show code
-- ppAbortedResult (CS.AbortedBranch loc _ t f) = "branch (@" ++ show loc ++ ") (t: " ++ ppAbortedResult t ++ ") (f: " ++ ppAbortedResult f ++ ")"


-- padWith :: Char -> Int -> String -> String
-- padWith c n s = replicate (n-length s) c ++ s

-- pad :: Int -> String -> String
-- pad = padWith ' '
