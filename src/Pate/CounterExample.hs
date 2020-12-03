{-|
Module           : Pate.CounterExample
Copyright        : (c) Galois, Inc 2020
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Presenting counter-examples to failed equivalence checks
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

module Pate.CounterExample 
  ( throwInequivalenceResult
  , getInequivalenceResult
  , ppEquivalenceError
  , ppAbortedResult
  , ppPreRegs
  , showModelForPtr
  , ppMemDiff
  ) where

import           GHC.Stack

import           Control.Monad.IO.Class ( liftIO )
import           Control.Lens hiding ( op, pre )
import           Control.Monad.Reader
import           Control.Applicative

import qualified Data.BitVector.Sized as BVS
import qualified Data.Set as S
import           Data.Maybe (catMaybes)
import           Data.Monoid

import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.TraversableF as TF

import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.Simulator as CS

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFG as MM

import qualified What4.Interface as W4
import qualified What4.Partial as W4P

import           Pate.Equivalence
import           Pate.Monad
import           Pate.SimState
import           Pate.Types
import qualified Pate.Memory.MemTrace as MT

throwInequivalenceResult ::
  Maybe (InequivalenceResult arch) ->
  EquivM sym arch ()
throwInequivalenceResult Nothing = return ()
throwInequivalenceResult (Just ir) = throwHere $ InequivalentError ir

getInequivalenceResult ::
  forall sym arch.
  HasCallStack =>
  InequivalenceReason ->
  EquivRelation sym arch ->
  SimBundle sym arch ->
  SymGroundEvalFn sym ->
  EquivM sym arch (InequivalenceResult arch)
getInequivalenceResult defaultReason eqRel bundle fn@(SymGroundEvalFn fn')  = do
  ecaseO <- liftIO $ MT.groundExitCase fn' (simOutExit $ simOutO $ bundle)
  ecaseP <- liftIO $ MT.groundExitCase fn' (simOutExit $ simOutP $ bundle)
  
  memdiff <- groundTraceDiff fn eqRel bundle
  regdiff <- MM.traverseRegsWith
    (\r preO -> do
        let
          preP = preRegsP ^. MM.boundValue r
          postO = postRegsO ^. MM.boundValue r
          postP = postRegsP ^. MM.boundValue r
        eqReg <- liftIO $ applyRegEquivRelation (eqRelRegs eqRel) r postO postP
        d <- mkRegisterDiff fn r preO preP postO postP eqReg
        return d
    ) preRegsO
    
  retO <- groundReturnPtr fn (simOutReturn $ simOutO bundle)
  retP <- groundReturnPtr fn (simOutReturn $ simOutP bundle)

  let reason =
        if isMemoryDifferent memdiff then InequivalentMemory
        else if areRegistersDifferent regdiff then InequivalentRegisters
        else defaultReason
  return $ InequivalentResults memdiff (ecaseO, ecaseP) regdiff (retO, retP) reason
  where
    preRegsO = simInRegs $ simInO bundle
    preRegsP = simInRegs $ simInP bundle

    postRegsO = simOutRegs $ simOutO bundle
    postRegsP = simOutRegs $ simOutP bundle
    
isMemoryDifferent :: forall arch. MemTraceDiff arch -> Bool
isMemoryDifferent diffs = any (not . mIsValid) diffs

areRegistersDifferent :: forall arch. MM.RegState (MM.ArchReg arch) (RegisterDiff arch) -> Bool
areRegistersDifferent regs = case MM.traverseRegsWith_ go regs of
  Just () -> False
  Nothing -> True
  where
    go :: forall tp. MM.ArchReg arch tp -> RegisterDiff arch tp -> Maybe ()
    go _ diff = if rPostEquivalent diff then Just () else Nothing


groundTraceDiff :: forall sym arch.
  SymGroundEvalFn sym ->
  EquivRelation sym arch ->
  SimBundle sym arch ->
  EquivM sym arch (MemTraceDiff arch)
groundTraceDiff fn eqRel bundle = do
  footprints <- getFootprints bundle
  (S.toList . S.fromList . catMaybes) <$> mapM checkFootprint (S.toList $ footprints)
  where
    memO = simOutMem $ simOutO bundle
    memP = simOutMem $ simOutP bundle
    preMemO = simInMem $ simInO bundle
    preMemP = simInMem $ simInP bundle
    
    checkFootprint ::
      MT.MemFootprint sym (MM.ArchAddrWidth arch) ->
      EquivM sym arch (Maybe (MemOpDiff arch))
    checkFootprint (MT.MemFootprint ptr w dir cond) = do
      let repr = MM.BVMemRepr w MM.BigEndian
      stackRegion <- asks envStackRegion
      gstackRegion <- execGroundFn fn stackRegion
      -- "reads" here are simply the memory pre-state
      (oMem, pMem) <- case dir of
            MT.Read -> return $ (preMemO, preMemP)
            MT.Write -> return $ (memO, memP)
      val1 <- withSymIO $ \sym -> MT.readMemArr sym oMem ptr repr
      val2 <- withSymIO $ \sym -> MT.readMemArr sym pMem ptr repr
      cond' <- memOpCondition cond
      execGroundFn fn cond' >>= \case
        True -> do
          gptr <- groundLLVMPointer fn ptr
          let cell = MemCell ptr w
          memRel <- case ptrRegion gptr == gstackRegion of
            True -> return $ eqRelStack eqRel
            False -> return $ eqRelMem eqRel
          isValid <- liftIO $ applyMemEquivRelation memRel cell val1 val2
          groundIsValid <- execGroundFn fn isValid
          op1  <- groundMemOp fn ptr cond' val1
          op2  <- groundMemOp fn ptr cond' val2
          return $ Just $ MemOpDiff { mIsRead = case dir of {MT.Write -> False; _ -> True}
                                    , mOpOriginal = op1
                                    , mOpRewritten = op2
                                    , mIsValid = groundIsValid
                                    , mDesc = ""
                                    }
        False -> return Nothing


groundMemOp ::
  HasCallStack =>
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
  W4.Pred sym ->
  CLM.LLVMPtr sym w ->
  EquivM sym arch (GroundMemOp arch)
groundMemOp fn addr cond val = liftA3 GroundMemOp
  (groundLLVMPointer fn addr)
  (execGroundFn fn cond)
  (groundBV fn val)

groundBV ::
  HasCallStack =>
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym w ->
  EquivM sym arch (GroundBV w)
groundBV fn (CLM.LLVMPointer reg off) = do
  W4.BaseBVRepr w <- return $ W4.exprType off
  greg <- execGroundFn fn reg
  goff <- execGroundFn fn off
  let gbv = mkGroundBV w greg goff
  return gbv

groundLLVMPointer :: forall sym arch.
  HasCallStack =>
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
  EquivM sym arch (GroundLLVMPointer (MM.ArchAddrWidth arch))
groundLLVMPointer fn ptr = groundBVAsPointer <$> groundBV fn ptr


mkRegisterDiff ::
  HasCallStack =>
  SymGroundEvalFn sym ->
  MM.ArchReg arch tp ->
  MacawRegEntry sym tp ->
  -- ^ original prestate
  MacawRegEntry sym tp ->
  -- ^ patched prestate
  MacawRegEntry sym tp ->
  -- ^ original post state
  MacawRegEntry sym tp ->
  -- ^ patched post state
  W4.Pred sym ->
  EquivM sym arch (RegisterDiff arch tp)
mkRegisterDiff fn reg preO preP postO postP equivE = do
  pre <- concreteValue fn preO
  pre' <- concreteValue fn preP
  post <- concreteValue fn postO
  post' <- concreteValue fn postP
  equiv <- execGroundFn fn equivE
  
  desc <- liftIO $ ppRegDiff fn postO postP
  pure RegisterDiff
    { rReg = reg
    , rTypeRepr = macawRegRepr preP
    , rPreOriginal = pre
    , rPrePatched = pre'
    , rPostOriginal = post
    , rPostPatched = post'
    , rPostEquivalent = equiv
    , rDiffDescription = desc
    }

concreteValue ::
  HasCallStack =>
  SymGroundEvalFn sym ->
  MacawRegEntry sym tp ->
  EquivM sym arch (ConcreteValue (MS.ToCrucibleType tp))
concreteValue fn e
  | CLM.LLVMPointerRepr _ <- macawRegRepr e
  , ptr <- macawRegValue e = do
    groundBV fn ptr
concreteValue _ e = throwHere (UnsupportedRegisterType (Some (macawRegRepr e)))

groundReturnPtr ::
  HasCallStack =>
  SymGroundEvalFn sym ->
  CS.RegValue sym (CC.MaybeType (CLM.LLVMPointerType (MM.ArchAddrWidth arch))) ->
  EquivM sym arch (Maybe (GroundLLVMPointer (MM.ArchAddrWidth arch)))
groundReturnPtr fn (W4P.PE p e) = execGroundFn fn p >>= \case
  True -> Just <$> groundLLVMPointer fn e
  False -> return Nothing
groundReturnPtr _ W4P.Unassigned = return Nothing

-------------------------------------------------
-- Printing

ppEquivalenceError ::
  MS.SymArchConstraints arch =>
  ShowF (MM.ArchReg arch) =>
  EquivalenceError arch -> String
ppEquivalenceError err | (InequivalentError ineq)  <- errEquivError err =
 "x\n" ++ ppInequivalenceResult ineq
ppEquivalenceError err = "-\n\t" ++ show err ++ "\n" -- TODO: pretty-print the error

ppInequivalenceResult ::
  MS.SymArchConstraints arch =>
  ShowF (MM.ArchReg arch) =>
  InequivalenceResult arch -> String
ppInequivalenceResult (InequivalentResults traceDiff exitDiffs regDiffs _retDiffs reason) =
  "x\n" ++ ppReason reason ++ "\n" ++ ppExitCaseDiff exitDiffs ++ "\n" ++ ppPreRegs regDiffs ++ ppMemTraceDiff traceDiff ++ ppDiffs regDiffs

ppReason :: InequivalenceReason -> String
ppReason r = "\tEquivalence Check Failed: " ++ case r of
  InequivalentRegisters -> "Final registers diverge."
  InequivalentMemory -> "Final memory states diverge."
  InvalidCallPair -> "Unexpected next IPs."
  InvalidPostState -> "Post state is invalid."
  PostRelationUnsat -> "Post-equivalence relation cannot be satisifed"

ppExitCaseDiff :: ExitCaseDiff -> String
ppExitCaseDiff (eO, eP) | eO == eP = "\tBlock Exited with " ++ ppExitCase eO
ppExitCaseDiff (eO, eP) =
  "\tBlocks have different exit conditions: "
  ++ ppExitCase eO ++ " (original) vs. "
  ++ ppExitCase eP ++ " (rewritten)"

ppExitCase :: MT.ExitCase -> String
ppExitCase ec = case ec of
  MT.ExitCall -> "function call"
  MT.ExitReturn -> "function return"
  MT.ExitArch -> "syscall"
  MT.ExitUnknown -> "unknown"

ppMemTraceDiff :: MemTraceDiff arch -> String
ppMemTraceDiff diffs = "\tTrace of memory operations:\n" ++ concatMap ppMemOpDiff diffs

ppMemOpDiff :: MemOpDiff arch -> String
ppMemOpDiff diff
  | shouldPrintMemOp diff
  =  "\t\t" ++ ppDirectionVerb (mIsRead diff) ++ " "
  ++ ppGroundMemOp (mIsRead diff) (mOpOriginal diff)
  ++ (if mOpOriginal diff == mOpRewritten diff
      then ""
      else
        " (original) vs. " ++ ppGroundMemOp (mIsRead diff) (mOpRewritten diff) ++ " (rewritten)"
         ++ "\n" ++ mDesc diff
     )
  ++ "\n"
ppMemOpDiff _ = ""

shouldPrintMemOp :: MemOpDiff arch -> Bool
shouldPrintMemOp diff =
  mOpOriginal diff /= mOpRewritten diff ||
  gCondition (mOpOriginal diff) ||
  gCondition (mOpRewritten diff)

ppGroundMemOp :: Bool -> GroundMemOp arch -> String
ppGroundMemOp isRead op
  | Some v <- gValue op
  =  show v
  ++ " " ++ ppDirectionPreposition isRead ++ " "
  ++ ppLLVMPointer (gAddress op)
  ++ if gCondition op
     then ""
     else " (skipped)"

ppDirectionVerb :: Bool -> String
ppDirectionVerb True = "read"
ppDirectionVerb False = "wrote"

ppDirectionPreposition :: Bool -> String
ppDirectionPreposition True = "from"
ppDirectionPreposition False = "to"

_ppEndianness :: MM.Endianness -> String
_ppEndianness MM.BigEndian = "→"
_ppEndianness MM.LittleEndian = "←"

ppPreRegs ::
  HasCallStack =>
  MM.RegState (MM.ArchReg arch) (RegisterDiff arch)
  -> String
ppPreRegs diffs = "\tInitial registers of a counterexample:\n" ++ case TF.foldMapF ppPreReg diffs of
  (Sum 0, s) -> s
  (Sum n, s) -> s ++ "\t\t(and " ++ show n ++ " other all-zero slots)\n"

ppPreReg ::
  HasCallStack =>
  RegisterDiff arch tp ->
  (Sum Int, String)
ppPreReg diff = case rTypeRepr diff of
  CLM.LLVMPointerRepr _
    | GroundBV _ obv <- rPreOriginal diff
    , GroundBV _ pbv <- rPrePatched diff ->
      case (BVS.asUnsigned obv, BVS.asUnsigned pbv) of
        (0, 0) -> (1, "")
        _ | obv == pbv -> (0, ppSlot diff ++ show (rPreOriginal diff) ++ "\n")
        _ -> (0, ppSlot diff ++ show (rPreOriginal diff) ++ "(original) vs. " ++ show (rPrePatched diff) ++ "\n")
  CLM.LLVMPointerRepr _ ->
    case (rPreOriginal diff) == (rPrePatched diff) of
      True -> (0, ppSlot diff ++ show (rPreOriginal diff)  ++ "\n")
      False -> (0, ppSlot diff ++ show (rPreOriginal diff)  ++ "(original) vs. " ++ show (rPrePatched diff) ++ "\n")

  _ -> (0, ppSlot diff ++ "unsupported register type in precondition pretty-printer\n")

ppDiffs ::
  MS.SymArchConstraints arch =>
  MM.RegState (MM.ArchReg arch) (RegisterDiff arch) ->
  String
ppDiffs diffs =
  "\tFinal IPs: "
  ++ show (rPostOriginal (diffs ^. MM.curIP))
  ++ " (original) vs. "
  ++ show (rPostPatched (diffs ^. MM.curIP))
  ++ " (rewritten)\n"
  ++ "\tMismatched resulting registers:\n" ++ TF.foldMapF ppDiff diffs

ppDiff ::
  RegisterDiff arch tp ->
  String
ppDiff diff | rPostEquivalent diff = ""
ppDiff diff = ppSlot diff ++ case rTypeRepr diff of
  CLM.LLVMPointerRepr _ -> ""
    ++ show (rPostOriginal diff)
    ++ " (original) vs. "
    ++ show (rPostPatched diff)
    ++ " (rewritten)\n"
    ++ rDiffDescription diff
    ++ "\n\n"
  _ -> "unsupported register type in postcondition comparison pretty-printer\n"

ppRegEntry :: SymGroundEvalFn sym -> MacawRegEntry sym tp -> IO String
ppRegEntry fn (MacawRegEntry repr v) = case repr of
  CLM.LLVMPointerRepr _ | CLM.LLVMPointer _ offset <- v -> showModelForExpr fn offset
  _ -> return "Unsupported register type"


showModelForPtr :: forall sym w.
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym w ->
  IO String
showModelForPtr fn (CLM.LLVMPointer reg off) = do
  regStr <- showModelForExpr fn reg
  offStr <- showModelForExpr fn off
  return $ "Region:\n" ++ regStr ++ "\n" ++ offStr

ppMemDiff ::
  SymGroundEvalFn sym ->
  CLM.LLVMPtr sym ptrW ->
  CLM.LLVMPtr sym w ->
  CLM.LLVMPtr sym w ->
  IO String
ppMemDiff fn ptr val1 val2 = do
  ptrStr <- showModelForPtr fn ptr
  val1Str <- showModelForPtr fn val1
  val2Str <- showModelForPtr fn val2
  return $ "Pointer: " ++ ptrStr ++ "\nValue (original)" ++ val1Str ++ "\nValue (patched)" ++ val2Str

ppRegDiff ::
  SymGroundEvalFn sym ->
  MacawRegEntry sym tp ->
  MacawRegEntry sym tp ->
  IO String
ppRegDiff fn reg1 reg2 = do
  origStr <- ppRegEntry fn reg1
  patchedStr <- ppRegEntry fn reg2
  return $ "Original: \n" ++ origStr ++ "\n\nPatched: \n" ++ patchedStr

ppSlot ::
  RegisterDiff arch tp
  -> String
ppSlot (RegisterDiff { rReg = reg })  = "\t\tslot " ++ (pad 4 . showF) reg ++ ": "

ppAbortedResult :: CS.AbortedResult sym ext -> String
ppAbortedResult (CS.AbortedExec reason _) = show reason
ppAbortedResult (CS.AbortedExit code) = show code
ppAbortedResult (CS.AbortedBranch loc _ t f) = "branch (@" ++ show loc ++ ") (t: " ++ ppAbortedResult t ++ ") (f: " ++ ppAbortedResult f ++ ")"


padWith :: Char -> Int -> String -> String
padWith c n s = replicate (n-length s) c ++ s

pad :: Int -> String -> String
pad = padWith ' '
