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

module Pate.Proof
  ( EquivTripleBody(..)
  , EquivTriple
  , SomeProofBlockSlice(..)
  , VerificationStatus(..)
  , ProofBlockSliceBody(..)
  , ProofBlockSlice
  , ProofFunctionCall(..)
  , SomeProofGoal(..)
  , trivialSliceBody
  , prfPre
  , prfBodyPre
  ) where

import qualified Data.Map as Map

import           Data.Parameterized.Some
import           Data.Parameterized.Classes

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import qualified Data.Macaw.CFG as MM

import qualified Pate.Types as PT
import qualified Pate.Equivalence as PE
import qualified Pate.SimState as PS

import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4B

---------------------------------------------
-- proof objects

data VerificationStatus arch =
    Unverified
  | VerificationSuccess
  | VerificationFail (PT.InequivalenceResult arch)

-- | The body of an 'EquivTriple'.
data EquivTripleBody sym arch where
  EquivTripleBody ::
    {
      eqPair :: PT.PatchPair arch
      -- ^ the entry points that yield equivalent states on the post-domain
      -- after execution, assuming initially equivalent states on the pre-domain
    , eqPreDomain :: PE.StatePred sym arch
      -- ^ the pre-domain: the state that was assumed initially equivalent
      -- closed over the bound variables representing the initial state
    , eqPostDomain :: PE.StatePredSpec sym arch
      -- ^ the post-domain: the state that was proven equivalent after execution
      -- abstracted over the bound variables representing the final state
    , eqStatus :: VerificationStatus arch
      -- ^ flag indicating whether or not this triple has passed verification
    , eqValidSym :: PT.Sym sym
    } -> EquivTripleBody sym arch

instance PT.ExprMappable sym (EquivTripleBody sym arch) where
  mapExpr sym f triple = do
    eqPreDomain' <- PT.mapExpr sym f (eqPreDomain triple)
    eqPostDomain' <- PT.mapExpr sym f (eqPostDomain triple)
    return $ EquivTripleBody (eqPair triple) eqPreDomain' eqPostDomain' (eqStatus triple) (eqValidSym triple)

-- | An triple representing the equivalence conditions for a block pair. Abstracted
-- over the initial machine state.
type EquivTriple sym arch = PS.SimSpec sym arch (EquivTripleBody sym arch)

data ProofFunctionCall sym arch =
    ProofFunctionCall
      {
        -- | proof that the correct pre-domain is established equivalent
        -- prior to the function call
        prfFunPre :: EquivTripleBody sym arch
        -- | proof that the function itself establishes equivalence on the target
        -- post-domain. Note that it is a 'ProofBlockSlice' since we do not need to
        -- bind the initial machine state that was in scope for this call.
      , prfFunBody :: ProofBlockSlice sym arch
        -- | proof that the target post-domain following the function call
        -- establishes the overall target post-domain equivalence. Again this does not
        -- bind the initial state.
      , prfFunCont :: ProofBlockSlice sym arch
      }
  | ProofTailCall
      { prfFunPre :: EquivTripleBody sym arch
      , prfFunBody :: ProofBlockSlice sym arch
      } 

instance PT.ExprMappable sym (ProofFunctionCall sym arch) where
  mapExpr sym f prf = do
    prfFunPre' <- PT.mapExpr sym f (prfFunPre prf)
    prfFunCont' <- PT.mapExpr sym f (prfFunCont prf)
    case prf of
      ProofFunctionCall{} -> do
        prfFunBody' <- PT.mapExpr sym f (prfFunBody prf)
        return $ ProofFunctionCall prfFunPre' prfFunBody' prfFunCont'
      ProofTailCall{} -> return $ ProofTailCall prfFunPre' prfFunCont'

-- | Trace of the proof that a pair of block "slices" satisfy the
-- given triple. 
data ProofBlockSliceBody sym arch =
  ProofBlockSliceBody
      { -- | the top-level triple for this slice, stating that
        -- all possible exits satisfy equivalence on the post-domain
        -- given equivalence on the pre-domain
        prfTriple :: EquivTripleBody sym arch
        -- | all jumps which exit the slice with a function call
      , prfFunCalls :: [ProofFunctionCall sym arch]
      , prfReturn :: Maybe (EquivTripleBody sym arch)
      , prfUnknownExit :: Maybe (EquivTripleBody sym arch)
      }

instance PT.ExprMappable sym (ProofBlockSliceBody sym arch) where
  mapExpr sym f prf = do
    prfTriple' <- PT.mapExpr sym f (prfTriple prf)
    prfFunCalls' <- mapM (PT.mapExpr sym f) (prfFunCalls prf)
    prfReturn' <- mapM (PT.mapExpr sym f) (prfReturn prf)
    prfUnknownExit' <- mapM (PT.mapExpr sym f) (prfUnknownExit prf)
    return $ ProofBlockSliceBody prfTriple' prfFunCalls' prfReturn' prfUnknownExit'

trivialSliceBody :: EquivTripleBody sym arch -> ProofBlockSliceBody sym arch
trivialSliceBody triple = ProofBlockSliceBody triple [] Nothing Nothing

prfBodyPre :: ProofBlockSliceBody sym arch -> PE.StatePred sym arch
prfBodyPre = eqPreDomain . prfTriple

-- | A trace for the proof of a given triple, abstracted over an initial machine state.
type ProofBlockSlice sym arch = PS.SimSpec sym arch (ProofBlockSliceBody sym arch)

prfPre :: ProofBlockSlice sym arch -> PE.StatePredSpec sym arch
prfPre = PS.specMap prfBodyPre

-- | 'EquivTriple' abstracted over the specific expression builder. Used for reporting.
data SomeProofBlockSlice arch where
  SomeProofBlockSlice ::
    PT.Sym sym -> ProofBlockSlice sym arch -> SomeProofBlockSlice arch
instance PT.ValidArch arch => Show (SomeProofBlockSlice arch) where
  show (SomeProofBlockSlice vsym prf) = show (ppProofBlockSlice vsym prf)


data SomeProofGoal arch where
  SomeProofGoal ::
    PT.Sym sym ->
    EquivTriple sym arch ->
    ProofBlockSlice sym arch ->
    SomeProofGoal arch
instance PT.ValidArch arch => Show (SomeProofGoal arch) where
  show (SomeProofGoal vsym triple prf) = show (ppProofGoal vsym triple prf)

----------------------------------------------
-- printing

data ProofAnn

type ProofDoc = PP.Doc ProofAnn

ppMaybe :: Maybe f -> (f -> ProofDoc) -> ProofDoc
ppMaybe (Just f) pp = pp f
ppMaybe Nothing _ = PP.emptyDoc


ppProofGoal ::
  PT.ValidArch arch =>
  PT.Sym sym ->
  EquivTriple sym arch ->
  ProofBlockSlice sym arch ->
  ProofDoc
ppProofGoal vsym triple prf =
  PP.vsep
    [ "Top-level equivalence goal: "
    , PP.indent 2 $ ppEquivTriple vsym triple
    , "Equivalence proof:"
    , PP.indent 2 $ ppProofBlockSlice vsym prf
    ]

ppProofBlockSlice ::
  PT.ValidArch arch =>
  PT.Sym sym ->
  ProofBlockSlice sym arch ->
  ProofDoc
ppProofBlockSlice vsym prf =
  PP.vsep
    [ ppEquivTriple vsym (PS.specMap prfTriple prf)
    , "Proof:"
    , PP.indent 4 $ PP.vsep
      [ "Function Calls: "
      , PP.indent 4 $ PP.list (map (ppProofFunctionCallSpec vsym . PS.attachSpec prf) (prfFunCalls prfBody))
      , ppMaybe (prfReturn prfBody) $ \trip ->
          PP.vsep
            [ "Function Return: "
            , PP.indent 4 $ ppEquivTriple vsym (PS.attachSpec prf trip)
            ]
      , ppMaybe (prfUnknownExit prfBody) $ \trip ->
          PP.vsep
            [ "Unknown function exit: "
            , PP.indent 4 $ ppEquivTriple vsym (PS.attachSpec prf trip)
            ]
      ]
    ]
  where
    prfBody = PS.specBody prf

-- we need to plumb through the initial variables, since they
-- are used when describing the triple that proves this function call
-- is valid
ppProofFunctionCallSpec ::
  PT.ValidArch arch =>
  PT.Sym sym ->
  PS.SimSpec sym arch (ProofFunctionCall sym arch) ->
  ProofDoc
ppProofFunctionCallSpec vsym prfCallSpec =
  PP.vsep $ 
    [ "Function pre-domain is satisfied before call:"
    , PP.indent 4 $ ppEquivTriple vsym $ PS.specMap prfFunPre prfCallSpec
    , "Function satisfies post-domain upon return:"
    , PP.indent 4 $ ppProofBlockSlice vsym $ prfFunBody prfCall
    ] ++ case prfCall of
      ProofFunctionCall{} ->
        [ "Continuing after function return satisfies post-domain for caller."
        , PP.indent 4 $ ppProofBlockSlice vsym $ prfFunBody prfCall
        ]
      ProofTailCall{} -> []
  where
    prfCall = PS.specBody prfCallSpec

ppEquivTriple :: PT.ValidArch arch => PT.Sym sym -> EquivTriple sym arch -> ProofDoc
ppEquivTriple vsym triple =
  PP.vsep
    [ "Block Pair:" <+> (ppPatchPair (eqPair tripleBody))
    , "Pre-domain:"
    , PP.indent 4 $ ppStatePredSpec vsym (PS.specMap eqPreDomain triple)
    , "Post-domain:"
    , PP.indent 4 $ ppStatePredSpec vsym (eqPostDomain tripleBody)
    ]
  where
    tripleBody = PS.specBody triple

ppStatePredSpec ::
  forall sym arch.
  PT.ValidArch arch =>
  PT.Sym sym ->
  PE.StatePredSpec sym arch ->
  ProofDoc
ppStatePredSpec (PT.Sym _sym) stpred =
  PP.vsep
    [ ppRegs
    , ppStack
    , ppMem
    ]
    where
      stPredBody = PS.specBody stpred
      regs = PE.predRegs stPredBody

      ppReg :: (Some (MM.ArchReg arch), W4.Pred sym) -> ProofDoc
      ppReg (Some reg, p) = case W4.asConstantPred p of
        Just False -> PP.emptyDoc
        _ -> PP.pretty $ showF reg
      
      ppRegs :: ProofDoc
      ppRegs = "Registers: " <> PP.line <> PP.indent 2 (PP.vsep (map ppReg (Map.toList regs)))

      ppStack :: ProofDoc
      ppStack = "Stack:" <> PP.line <> PP.indent 2 "dummy"

      ppMem :: ProofDoc
      ppMem = "Global Memory:" <> PP.line <> PP.indent 2 "dummy"      
        
ppPatchPair :: PT.ValidArch arch => PT.PatchPair arch -> ProofDoc
ppPatchPair pPair =
  PP.hsep
    [ "Original:" 
    , PP.pretty $ PT.ppBlock (PT.pOrig pPair)
    , "vs."
    , "Patched:"
    , PP.pretty $ PT.ppBlock (PT.pPatched pPair)
    ]
