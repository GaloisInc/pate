{-|
Module           : What4.UninterpFns
Copyright        : (c) Galois, Inc 2023
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Globally-unique uninterpreted functions, keyed on name, signature and expression builder
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module What4.UninterpFns (
  mkUninterpretedSymFn
) where

import qualified Control.Concurrent.MVar as MVar
import           Control.Concurrent.MVar (MVar)
import qualified System.IO.Unsafe as IO

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Map (MapF)

import qualified What4.Interface as W4
import qualified What4.ProgramLoc as W4
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Parameterized.TraversableFC as TFC

data UninterpFn sym (ctx :: Ctx.Ctx W4.BaseType) where
  UninterpFn :: W4.SymFn sym args ret -> UninterpFn sym (args Ctx.::> ret)

data FnSig (ctx :: Ctx.Ctx W4.BaseType) where
  FnSig :: String -> Ctx.Assignment W4.BaseTypeRepr (args Ctx.::> ret) -> FnSig (args Ctx.::> ret) 

instance TestEquality FnSig where
  testEquality sig1 sig2 | EQF <- compareF sig1 sig2 = Just Refl
  testEquality _ _ = Nothing

instance OrdF FnSig where
  compareF (FnSig nm1 sig1) (FnSig nm2 sig2) = case compare nm1 nm2 of
    LT -> LTF
    GT -> GTF
    _ -> compareF sig1 sig2

data UninterpFnMap = forall sym. W4.IsSymExprBuilder sym => UninterpFnMap sym (MapF FnSig (UninterpFn sym))

globalFnMap :: MVar [UninterpFnMap]
globalFnMap = IO.unsafePerformIO (MVar.newMVar [])

-- | Determine expression builder equality by testing if their "programLoc" references overlap
--   FIXME: This is thread-unsafe since it modifies the program location without any guards
testSymEquality :: (W4.IsSymExprBuilder sym1, W4.IsSymExprBuilder sym2) => sym1 -> sym2 -> IO (Maybe (sym1 :~: sym2))
testSymEquality sym1 sym2 = do
  loc1 <- W4.getCurrentProgramLoc sym1
  loc2 <- W4.getCurrentProgramLoc sym2
  W4.setCurrentProgramLoc sym1 W4.initializationLoc
  W4.setCurrentProgramLoc sym2 W4.initializationLoc
  let dummyLoc = W4.mkProgramLoc "testSymEquality" W4.InternalPos
  W4.setCurrentProgramLoc sym1 dummyLoc
  loc2_updated <- W4.getCurrentProgramLoc sym2
  result <- case loc2_updated == dummyLoc of
    True -> return $ Just (unsafeCoerce Refl)
    False -> return Nothing
  W4.setCurrentProgramLoc sym1 loc1
  W4.setCurrentProgramLoc sym2 loc2
  return result


coerceToSym :: 
  W4.IsSymExprBuilder sym => 
  sym -> 
  UninterpFnMap -> 
  IO (Maybe (MapF FnSig (UninterpFn sym)))
coerceToSym sym1 (UninterpFnMap sym2 m) = do
  testSymEquality sym1 sym2 >>= \case
    Just Refl -> return $ Just m
    Nothing -> return Nothing

mkFreshUninterFn ::
  W4.IsSymExprBuilder sym => 
  sym ->
  FnSig ctx ->
  IO (UninterpFn sym ctx)
mkFreshUninterFn sym (FnSig nm (args Ctx.:> ret)) = do
  let args_flat = flattenStructRepr args
  case args_flat of
    Ctx.Empty -> do
      Ctx.Empty <- return args
      c <- W4.freshConstant sym (W4.safeSymbol nm) ret
      UninterpFn <$> W4.definedFn sym (W4.safeSymbol nm) Ctx.Empty c W4.AlwaysUnfold
    (_ Ctx.:> _) -> do
      -- we flatten all of the arguments to make the grounding infrastructure compatible
      -- with these functions
      arr <- W4.freshConstant sym (W4.safeSymbol nm) (W4.BaseArrayRepr args_flat ret)
      vars <- TFC.traverseFC (W4.freshBoundVar sym W4.emptySymbol) args
      vars_flat <- flattenStructs sym (TFC.fmapFC (W4.varExpr sym) vars)
      result <- W4.arrayLookup sym arr vars_flat
      UninterpFn <$> W4.definedFn sym (W4.safeSymbol nm) vars result W4.AlwaysUnfold

getUninterpFn :: 
  W4.IsSymExprBuilder sym => 
  sym ->
  FnSig ctx ->
  IO (UninterpFn sym ctx)
getUninterpFn sym fnSig = MVar.modifyMVar globalFnMap $ \fnMaps -> do
  go [] fnMaps >>= \case
    Just (fnMaps', r) -> case MapF.lookup fnSig r of
      Just fn -> return (fnMaps,fn)
      Nothing -> do
        fn <- mkFreshUninterFn sym fnSig
        return $ (UninterpFnMap sym (MapF.insert fnSig fn r):fnMaps', fn)
    Nothing -> do
      fn <- mkFreshUninterFn sym fnSig
      let r = UninterpFnMap sym (MapF.singleton fnSig fn)
      return $ (r:fnMaps,fn)
  where
    go _ [] = return Nothing
    go acc (m:fnMaps') = coerceToSym sym m >>= \case
      Just r -> return $ Just (acc ++ fnMaps', r)
      Nothing -> go (m:acc) fnMaps'

-- | Make an uninterpreted symbolic function that is globally-unique
--   based on its name, signature and expression builder
mkUninterpretedSymFn ::
  W4.IsSymExprBuilder sym =>
  sym ->
  String ->
  Ctx.Assignment W4.BaseTypeRepr args ->
  W4.BaseTypeRepr ret ->
  IO (W4.SymFn sym args ret)
mkUninterpretedSymFn sym nm args ret = do
  UninterpFn fn <- getUninterpFn sym (FnSig nm (args Ctx.:> ret))
  return fn


-- FIXME: copied from MemTrace
  -- avoiding struct-indexed arrays, which are unsupported by ground evaluation
type family FlatStructs tp :: Ctx.Ctx W4.BaseType where
  FlatStructs (W4.BaseStructType ctx) = FlatStructsCtx ctx
  FlatStructs (W4.BaseBVType w) = Ctx.EmptyCtx Ctx.::> (W4.BaseBVType w)
  FlatStructs W4.BaseIntegerType = Ctx.EmptyCtx Ctx.::> W4.BaseIntegerType
  FlatStructs W4.BaseBoolType = Ctx.EmptyCtx Ctx.::> W4.BaseBVType 1

type family FlatStructsCtx ctx :: Ctx.Ctx W4.BaseType where
  FlatStructsCtx Ctx.EmptyCtx = Ctx.EmptyCtx
  FlatStructsCtx (ctx Ctx.::> tp) = FlatStructsCtx ctx Ctx.<+> FlatStructs tp

flattenStructRepr :: Ctx.Assignment W4.BaseTypeRepr ctx -> Ctx.Assignment W4.BaseTypeRepr (FlatStructsCtx ctx)
flattenStructRepr Ctx.Empty = Ctx.Empty
flattenStructRepr (ctx Ctx.:> W4.BaseStructRepr ctx') = flattenStructRepr ctx Ctx.<++> flattenStructRepr ctx'
flattenStructRepr (ctx Ctx.:> (W4.BaseBVRepr w)) = flattenStructRepr ctx Ctx.:> (W4.BaseBVRepr w)
flattenStructRepr (ctx Ctx.:> W4.BaseIntegerRepr) = flattenStructRepr ctx Ctx.:> W4.BaseIntegerRepr
flattenStructRepr (ctx Ctx.:> W4.BaseBoolRepr) = flattenStructRepr ctx Ctx.:> W4.BaseBVRepr (W4.knownNat @1)
flattenStructRepr tp = error $ "flattenStructRepr: unsupported type:" ++ show tp

flattenStructs ::
  W4.IsExprBuilder sym =>
  sym ->
  Ctx.Assignment (W4.SymExpr sym) ctx ->
  IO (Ctx.Assignment (W4.SymExpr sym) (FlatStructsCtx ctx))
flattenStructs sym (ctx Ctx.:> e) = do
  ctx_flat <- flattenStructs sym ctx
  case W4.exprType e of
    W4.BaseStructRepr ctx' -> do
      fields <- Ctx.traverseWithIndex (\idx _ -> W4.structField sym e idx) ctx'
      ctx'_flat <- flattenStructs sym fields
      return $ ctx_flat Ctx.<++> ctx'_flat
    W4.BaseBVRepr _ -> return $ ctx_flat Ctx.:> e
    W4.BaseIntegerRepr -> return $ ctx_flat Ctx.:> e
    W4.BaseBoolRepr -> do
      bv <- W4.predToBV sym e (W4.knownNat @1)
      return $ ctx_flat Ctx.:> bv
    tp -> fail $ "flattenStructs: unsupported type:" ++ show tp
flattenStructs _sym Ctx.Empty = return Ctx.empty
