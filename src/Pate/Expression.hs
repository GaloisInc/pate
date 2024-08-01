{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Simple expression language for representing symbolic conditions.
module Pate.Expression (

) where

import           GHC.TypeNats
import           Control.Applicative
import qualified Data.Text as Text
import           Text.Read

import qualified Data.Aeson as JSON
import           Data.Aeson ( (.=), (.:))
import           Data.Parameterized.Some
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.Context as Ctx
import qualified Data.BitVector.Sized as BVS
import qualified Data.Parameterized.TraversableFC as TFC
import           Data.Parameterized.TH.GADT
import           Data.Parameterized.WithRepr

import Control.Monad (forM)

data Type = 
    BVType Nat
  | RegionType
  | PointerType
  | BoolType
  | IntegerType

data TypeRepr (tp :: Type) where
  BVTypeRepr :: NR.NatRepr n -> TypeRepr (BVType n)
  RegionTypeRepr :: TypeRepr RegionType
  PointerTypeRepr :: TypeRepr PointerType
  BoolTypeRepr :: TypeRepr BoolType
  IntegerTypeRepr :: TypeRepr IntegerType

$(return [])

instance IsRepr TypeRepr


instance KnownNat n => KnownRepr TypeRepr (BVType n) where
  knownRepr = BVTypeRepr NR.knownNat

instance KnownRepr TypeRepr RegionType where
  knownRepr = RegionTypeRepr

instance KnownRepr TypeRepr PointerType where
  knownRepr = PointerTypeRepr

instance KnownRepr TypeRepr BoolType where
  knownRepr = BoolTypeRepr

instance KnownRepr TypeRepr IntegerType where
  knownRepr = IntegerTypeRepr

instance TestEquality TypeRepr where
  testEquality tp1 tp2 = case compareF tp1 tp2 of
    EQF -> Just Refl
    _ -> Nothing

instance OrdF TypeRepr where
  compareF = $(structuralTypeOrd [t|TypeRepr|] [(TypeApp (ConType [t|NR.NatRepr|]) AnyType, [|compareF|])])

instance JSON.ToJSON (TypeRepr tp) where
  toJSON = \case
    BVTypeRepr n -> JSON.object [ "bv" .= (NR.natValue n) ]
    RegionTypeRepr -> JSON.String "region"
    PointerTypeRepr -> JSON.String "pointer"
    BoolTypeRepr -> JSON.String "bool"
    IntegerTypeRepr -> JSON.String "int"

instance JSON.FromJSON (Some (TypeRepr)) where
  parseJSON v = do
    JSON.Object o <- return  v
    (n :: Natural) <- o .: "bv"
    Just (Some nrepr) <- return $ NR.someNat n
    return $ Some $ BVTypeRepr nrepr
    <|> do
      JSON.String s <- return  v
      case s of
        "region" -> return $ Some RegionTypeRepr
        "pointer" -> return $ Some PointerTypeRepr
        "bool" -> return $ Some BoolTypeRepr
        "int" -> return $ Some IntegerTypeRepr
        _ -> fail $ "TypeRepr: unexpected type: " ++ show s
    <|> fail "TypeRepr"


data ConcretePointer = 
    ConcretePointer32 (BVS.BV 32) Natural
  | ConcretePointer64 (BVS.BV 64) Natural


instance JSON.ToJSON ConcretePointer where
  toJSON = \case
    ConcretePointer32 bv n -> JSON.object [ "width" .= (32 :: Integer),  "offset" .= BVS.asUnsigned bv, "region" .= n ]
    ConcretePointer64 bv n -> JSON.object [ "width" .= (64 :: Integer),  "offset" .= BVS.asUnsigned bv, "region" .= n ]

instance JSON.FromJSON ConcretePointer where
  parseJSON v = do
    JSON.Object o <- return  v
    (width :: Integer) <- o .: "width"
    (offset :: Integer) <- o .: "offset"
    (region :: Natural) <- o .: "region"
    case width of
      32 -> return $ ConcretePointer32 (BVS.mkBV (NR.knownNat @32) offset) region
      64 -> return $ ConcretePointer64 (BVS.mkBV (NR.knownNat @64) offset) region
      _ -> fail $ "ConcretePointer: unexpected width:" ++ show width

data ConcreteValue tp where
  ConcreteBV :: NR.NatRepr n -> BVS.BV n -> ConcreteValue (BVType n)
  ConcretePointer :: ConcretePointer -> ConcreteValue PointerType
  ConcreteRegion :: Natural -> ConcreteValue RegionType
  ConcreteInteger :: Integer -> ConcreteValue IntegerType
  ConcreteBool :: Bool -> ConcreteValue BoolType

concreteValueType :: ConcreteValue tp -> TypeRepr tp
concreteValueType = \case
  ConcreteBV n _ -> BVTypeRepr n
  ConcretePointer _ -> PointerTypeRepr
  ConcreteRegion _ -> RegionTypeRepr
  ConcreteInteger _ -> IntegerTypeRepr
  ConcreteBool _ -> BoolTypeRepr

instance JSON.ToJSON (ConcreteValue tp) where
  toJSON = \case
    ConcreteBV n bv -> JSON.object [ "width" .= NR.natValue n,  "bv" .= BVS.asUnsigned bv]
    ConcretePointer ptr -> JSON.object [ "pointer" .= ptr ]
    ConcreteRegion r -> JSON.object [ "region" .= r ]
    ConcreteInteger i -> JSON.object [ "int" .= i ]
    ConcreteBool b -> JSON.object [ "bool" .= b ]

instance JSON.FromJSON (Some ConcreteValue) where
  parseJSON v = do
    JSON.Object o <- return v
    let
      parsebv = do
        (bv_int :: Integer) <- o .: "bv"
        (width_nat :: Natural) <- o .: "width"
        Just (Some (width :: NR.NatRepr n)) <- return $ NR.someNat width_nat
        return $ Some $ ConcreteBV width (BVS.mkBV width bv_int)
      parseptr = do
        (ptr :: ConcretePointer) <-  o.: "ptr"
        return $ Some $ ConcretePointer ptr
      parseregion = do
        (region :: Natural) <- o.: "region"
        return $ Some $ ConcreteRegion region
      parseint = do
        (integer :: Integer) <- o.: "int"
        return $ Some $ ConcreteInteger integer
      parsebool = do
        (bool :: Bool) <- o.: "bool"
        return $ Some $ ConcreteBool bool
    parsebv <|> parseptr <|> parseregion <|> parseint <|> parsebool

-- | Derive a simple json printer/parser from a type with a read and show instance
newtype FromReadShow x = FromReadShow { unRS :: x }

instance Show t => JSON.ToJSON (FromReadShow t) where
  toJSON (FromReadShow t) = JSON.String (Text.pack (show t))

instance Read t => JSON.FromJSON (FromReadShow t) where
  parseJSON v = do
    JSON.String t <- return v
    case readEither (Text.unpack t) of
      Right o -> return $ FromReadShow o
      Left err -> fail err

data BinOpTag =
  Add | Sub | Mul | Div | Mod | And | Or | LTs | LTu | GTs | GTu | LEs | LEu | GEs | GEu | NEQ | EQ
  deriving (Read, Show)

instance JSON.ToJSON BinOpTag where
  toJSON t = JSON.toJSON (FromReadShow t)

instance JSON.FromJSON BinOpTag where
  parseJSON v = unRS <$> JSON.parseJSON v

data BinOp tpL tpR tp where
  BinOp :: 
    { bopTag :: BinOpTag
    , bopTyArgL :: TypeRepr tpL
    , bopTyArgR :: TypeRepr tpR
    , bopTy :: TypeRepr tp
    } -> BinOp tpL tpR tp

instance JSON.ToJSON (BinOp tpL tpR tp) where
  toJSON bop = 
      JSON.object
        [ "tag" .= bopTag bop
        , "typeL" .= bopTyArgL bop
        , "typeR" .= bopTyArgR bop
        , "type" .= bopTy bop
        ]

data SomeBinOp = forall tpL tpR tp. SomeBinOp (BinOp tpL tpR tp)

instance JSON.FromJSON SomeBinOp where
  parseJSON v = do
    JSON.Object o <- return  v
    (tag :: BinOpTag) <- o .: "tag"
    Some (typeL :: TypeRepr tpL) <- o .: "typeL"
    Some (typeR :: TypeRepr tpR) <- o .: "typeR"
    Some (type_ :: TypeRepr tp) <- o .: "type"
    return $ SomeBinOp $ BinOp tag typeL typeR type_

data UnOpTag = Neg | Not | UExt | SExt | Cast
  deriving (Read, Show)

instance JSON.ToJSON UnOpTag where
  toJSON t = JSON.toJSON (FromReadShow t)

instance JSON.FromJSON UnOpTag where
  parseJSON v = unRS <$> JSON.parseJSON v

data UnOp tpArg tp where
  UnOp :: 
    { uopTag :: UnOpTag
    , uopTyArg :: TypeRepr tpArg
    , uopTy :: TypeRepr tp
    } -> UnOp tpArg tp

instance JSON.ToJSON (UnOp tpArg tp) where
  toJSON uop = 
      JSON.object
        [ "tag" .= uopTag uop
        , "typeArg" .= uopTyArg uop
        , "type" .= uopTy uop
        ]

data SomeUnOp = forall tpArg tp. SomeUnOp (UnOp tpArg tp)

instance JSON.FromJSON SomeUnOp where
  parseJSON v = do
    JSON.Object o <- return  v
    (tag :: UnOpTag) <- o .: "tag"
    Some (typeArg :: TypeRepr tpArg) <- o .: "typeArg"
    Some (type_ :: TypeRepr tp) <- o .: "type"
    return $ SomeUnOp $ UnOp tag typeArg type_

-- FIXME: duplicated from macaw
data Endianness = BigEndian | LittleEndian
  deriving (Read, Show)

instance JSON.ToJSON Endianness where
  toJSON o = JSON.String (Text.pack (show o))

instance JSON.FromJSON Endianness where
  parseJSON v = do
    JSON.String t <- return v
    case readEither (Text.unpack t) of
      Right o -> return o
      Left err -> fail err

data Var (tp :: Type) where
  Var :: { varName :: String, varIdent :: Integer, varType :: TypeRepr tp } -> Var tp
$(return [])

instance TestEquality Var where
  testEquality tp1 tp2 = case compareF tp1 tp2 of
    EQF -> Just Refl
    _ -> Nothing

instance OrdF Var where
  compareF = $(structuralTypeOrd [t|Var|] [(TypeApp (ConType [t|TypeRepr|]) AnyType, [|compareF|])])

instance JSON.ToJSON (Var tp) where
  toJSON v =
      JSON.object
        [ "name" .= varName v
        , "ident" .= varIdent v
        , "type" .= varType v
        ]

instance JSON.FromJSON (Some Var) where
  parseJSON v = do
    JSON.Object o <- return v
    (name :: String) <- o .: "name"
    (ident :: Integer) <- o.: "ident"
    Some (t :: TypeRepr tp) <- o.: "type"
    return $ Some $ Var name ident t

newtype VarBinds = VarBinds (MapF.MapF Var Expression)

instance JSON.ToJSON VarBinds where
  toJSON (VarBinds binds) = JSON.toJSON $ map (\(MapF.Pair a b) -> JSON.toJSON (a,b)) $ MapF.toList  binds

instance JSON.FromJSON VarBinds where
  parseJSON v = do
    (varExprs_json :: [(JSON.Value, JSON.Value)]) <- JSON.parseJSON v
    pairs <- forM varExprs_json $ \(var_json, expr_json) -> do
      Some (var :: Var tp) <- JSON.parseJSON var_json
      withRepr (varType var) $ do
        (e :: Expression tp) <- JSON.parseJSON expr_json
        return $ MapF.Pair var e
    return $ VarBinds $ MapF.fromList pairs

data Expression (tp :: Type) where
  Let :: VarBinds -> Expression tp -> Expression tp
  -- ^ Expression with let-bindings
  VarE :: Var tp -> Expression tp
  -- ^ Variable reference from binding environment
  ReadMemBV :: Endianness -> NR.NatRepr n -> Expression PointerType -> Expression ('BVType (8 NR.* n))
  -- ^ Reading raw bytes. For a non pointer-width read we know we can interpret the result as a bitvector, discarding
  -- the region information from the memory model
  ReadMemPtr :: Endianness -> Expression PointerType -> Expression PointerType
  -- ^ Reading a pointer. If a value is read from memory and then used as a pointer, then we need to retrieve its
  -- region information from the memory model as well as the bytes.
  Literal :: ConcreteValue tp -> Expression tp
  -- ^ Raw literal values. Currently the expression type doesn't depend on the architecture, so we leave it
  -- as a runtime check that literal pointers have the correct width.
  Register :: TypeRepr tp -> String -> Expression tp
  -- ^ Reading from registers. The strings are user-friendly names that the architecture definition can
  -- turn into formal registers (i.e. via 'Pate.Arch.readRegister')
  Undefined :: Ctx.Assignment Expression args -> TypeRepr tp -> String -> Expression tp
  -- ^ Undefined/arbitrary values. These can come from stubs that are under-specified: e.g. reading
  -- a file has an unknown number of bytes. In general these can be uninterpreted functions over
  -- the symbolic state, represented by the list of expressions here.
  Global :: TypeRepr tp -> String -> Expression tp
  -- ^ Reading from global variables. These are essentially virtual registers that
  -- are also tracked as part of the symbolic state. e.g. the highest region allocated
  -- from 'malloc', which is incremented each time it is called.
  AppBinOp :: 
    BinOp tpL tpR tp ->
    Expression tpL -> 
    Expression tpR -> 
    Expression tp
  -- ^ Applying a binary operation. Notably we don't have any static constraints
  -- to ensure that this is well-typed, meaning that the conversion to a what4 predicate
  -- can fail if this operation is not defined.
  AppUnOp :: UnOp tpArg tp -> Expression tpArg -> Expression tp
  -- ^ Applying a unary operation.

exprType :: Expression tp -> TypeRepr tp
exprType = \case
  Let _ e -> exprType e
  VarE v -> varType v
  ReadMemBV _ bytes _ -> BVTypeRepr (NR.natMultiply (NR.knownNat @8) bytes)
  ReadMemPtr{} -> PointerTypeRepr
  Literal c -> concreteValueType c
  Undefined _ tp _ -> tp
  Register tp _ -> tp
  Global tp _ -> tp
  AppBinOp bop _ _ -> bopTy bop
  AppUnOp uop _ -> uopTy uop


instance JSON.ToJSON (Expression tp) where
  toJSON = \case
    Let binds e -> JSON.object ["kind" .= ("let" :: String), "binds" .= binds, "expr" .= e]
    VarE v -> JSON.object [ "kind" .= ("var" :: String), "value" .= v]
    ReadMemBV endianness n ptrE -> 
      JSON.object [ "kind" .= ("readMemBV" :: String), "endianness" .= endianness, "bytes" .= NR.natValue n, "pointer".= ptrE ]
    ReadMemPtr endianness ptrE ->
      JSON.object [ "kind" .= ("readMemPtr" :: String), "endianness" .= endianness, "pointer".= ptrE ]
    Literal c -> JSON.object [ "kind" .= ("literal" :: String), "value" .= c] 
    Register tp nm -> JSON.object [ "kind" .= ("register" :: String), "type" .= tp, "name" .= nm ]
    Undefined args tp nm -> JSON.object [ "kind" .= ("undefined" :: String), "type" .= tp, "name" .= nm, "args" .= TFC.toListFC JSON.toJSON args ]
    Global tp nm -> JSON.object [ "kind" .= ("global" :: String), "type" .= tp, "name" .= nm ]
    AppBinOp bop eL eR -> JSON.object [ "kind" .= ("binop" :: String), "value" .= bop, "argL" .= eL, "argR" .= eR]
    AppUnOp uop arg -> JSON.object [ "kind" .= ("unop" :: String), "value" .= uop, "arg" .= arg]

instance KnownRepr TypeRepr tp => JSON.FromJSON (Expression tp) where
  parseJSON v = do
    Some (e :: Expression tp') <- JSON.parseJSON v
    case testEquality (exprType e) (knownRepr @_ @_ @tp) of
      Just Refl -> return e
      Nothing -> fail $ "Unexpected expression type"


instance JSON.FromJSON (Some (Expression)) where
  parseJSON v = do
    JSON.Object o <- return  v
    (kind :: String) <- o .: "kind"
    case kind of
      "let" -> do
        (binds :: VarBinds) <- o.: "binds"
        Some (e :: Expression tp) <- o.: "expr"
        return $ Some $ Let binds e
      "readMemBV" -> do
        (endianness :: Endianness) <- o .: "endianness"
        (bytes :: Natural) <- o .: "bytes"
        Just (Some (bytes_repr :: NR.NatRepr n)) <- return $ NR.someNat bytes
        (ptrE :: Expression PointerType) <- o .: "ptrE"
        return $ Some $ ReadMemBV endianness bytes_repr ptrE
      "readMemPtr" -> do
        (endianness :: Endianness) <- o .: "endianness"
        (ptrE :: Expression PointerType) <- o .: "ptrE"
        return $ Some $ ReadMemPtr endianness ptrE
      "literal" -> do
        Some (c :: ConcreteValue tp) <- o .: "value"
        return $ Some $ Literal c
      "register" -> do
        Some (tp :: TypeRepr tp) <- o .: "type"
        (name :: String) <- o .: "name"
        return $ Some $ Register tp name
      "undefined" -> do
        Some (tp :: TypeRepr tp) <- o .: "type"
        (name :: String) <- o .: "name"
        (args_json :: [Some Expression]) <- o.: "args"
        Some args <- return $ (Ctx.fromList args_json)
        return $ Some $ Undefined args tp name
      "global" -> do
        Some (tp :: TypeRepr tp) <- o .: "type"
        (name :: String) <- o .: "name"
        return $ Some $ Register tp name
      "binop" -> do
        SomeBinOp (binop :: BinOp tpL tpR tp) <- o.: "value"
        (eL :: Expression tpL) <- withRepr (bopTyArgL binop) $ o.: "argL"
        (eR :: Expression tpR) <- withRepr (bopTyArgR binop) $ o.: "argR"
        return $ Some $ AppBinOp binop eL eR
      "unop" -> do
        SomeUnOp (unop :: UnOp tpArg tp) <- o.: "value"
        (eArg :: Expression tpArg) <- withRepr (uopTyArg unop) $ o.: "arg"
        return $ Some $ AppUnOp unop eArg
      _ -> fail $ "Unexpected expression kind: " ++ kind

        

