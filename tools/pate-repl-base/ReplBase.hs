{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

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

import qualified System.IO.Unsafe as IO
import qualified Data.IORef as IO
import qualified System.IO as IO

import qualified Pate.Arch as PA
import qualified Pate.Solver as PS

data SomePrintFn = SomePrintFn (forall a. ((PS.ValidSym Sym, PA.ValidArch Arch) => Show a) => a -> IO ())

data Sym
data Arch


printFn :: ((PS.ValidSym Sym, PA.ValidArch Arch) => Show a) => a -> IO ()
printFn a = IO.readIORef printFnRef >>= \(SomePrintFn f) -> f a

printFnRef :: IO.IORef SomePrintFn
printFnRef = IO.unsafePerformIO (IO.newIORef (SomePrintFn $ \_a -> IO.putStrLn "Missing Print Function" >> return ()))

promptFnRef :: IO.IORef ([String] -> Int -> IO String)
promptFnRef = IO.unsafePerformIO (IO.newIORef (\_ _ -> return ">>"))
            
promptFn :: [String] -> Int -> IO String
promptFn a b = IO.readIORef promptFnRef >>= \f -> f a b
