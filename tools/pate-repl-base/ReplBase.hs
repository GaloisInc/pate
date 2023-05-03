{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module ReplBase 
  ( printFn
  , promptFn
  , printFnRef
  , promptFnRef
  , SomePrintFn(..)
  , Sym
  , Arch
  ) where

import           Data.Kind (Type)
import qualified System.IO.Unsafe as IO
import qualified Data.IORef as IO
import qualified System.IO as IO

import qualified Pate.Arch as PA
import qualified Pate.Solver as PS
import           What4.Expr.Builder as W4B

data SomePrintFn = SomePrintFn (forall a. ((PS.ValidSym Sym, PA.ValidArch Arch) => Show a) => a -> IO ())

data T
data Solver :: Type -> Type
data Fs

type Sym = W4B.ExprBuilder T Solver Fs
data Arch


printFn :: ((PS.ValidSym Sym, PA.ValidArch Arch) => Show a) => a -> IO ()
printFn a = IO.readIORef printFnRef >>= \(SomePrintFn f) -> f a

printFnRef :: IO.IORef SomePrintFn
printFnRef = IO.unsafePerformIO (IO.newIORef (SomePrintFn $ \_a -> IO.putStrLn "Missing Print Function" >> return ()))

promptFnRef :: IO.IORef ([String] -> Int -> IO String)
promptFnRef = IO.unsafePerformIO (IO.newIORef (\_ _ -> return ">>"))
            
promptFn :: [String] -> Int -> IO String
promptFn a b = IO.readIORef promptFnRef >>= \f -> f a b
