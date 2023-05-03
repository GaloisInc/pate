{-|
Module           : Pate.IOReplay
Copyright        : (c) Galois, Inc 2023
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Provides primitives for recording and re-playing interactive operations
in order to save and restore the verifier state

-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Pate.IOReplay (
  doIOAct1,
  doIOAct2,
  doIOAct3,
  IOActionValue(..),
  initActionStore
) where

import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char.Lexer as MP
import qualified Text.Megaparsec.Char as MPC
import qualified Data.Text as T
import GHC.IO (unsafePerformIO)

import           Data.Typeable
import           Control.Concurrent.MVar

import Data.Parameterized.Some


class (Typeable t, Eq t) => IOActionValue t where
  readActionValue :: MP.Parsec () T.Text t
  writeActionValue :: t -> T.Text

instance IOActionValue Int where
  readActionValue = MP.decimal
  writeActionValue i = T.pack (show i)

instance IOActionValue Bool where
  readActionValue = (MPC.string "t" >> return True) MP.<|> (MPC.string "f" >> return False)
  writeActionValue = \case
    True -> "t"
    False -> "f"

data IOActionArg = forall t. IOActionValue t => IOActionArg t

instance Eq IOActionArg where
  (IOActionArg (a :: a)) == (IOActionArg (b :: b)) = case eqT @a @b of
    Just Refl -> a == b
    Nothing -> False

data IOAction ret = IOActionValue ret =>
  IOAction { ioActionArgs  :: [IOActionArg], ioActionRet :: ret }

data IOActionStore = 
  IOActionStore { storeQueued :: [T.Text], storeActions :: [Some IOAction], storeDesync :: Bool }

ioActionStore :: MVar IOActionStore
ioActionStore = unsafePerformIO (newMVar (IOActionStore [] [] False))

initActionStore :: [T.Text] -> IO ()
initActionStore acts = modifyMVar_ ioActionStore (\_ -> return $ IOActionStore acts [] False)

parseIOAction :: forall ret. IOActionValue ret => [IOActionArg] -> Proxy ret -> MP.Parsec () T.Text (IOAction ret)
parseIOAction [] _ = do
  ret <- readActionValue
  return $ IOAction [] ret
parseIOAction (IOActionArg (_ :: t):args) retProxy = do
  t' <- readActionValue @t
  _ <- MPC.space
  IOAction args' ret <-  parseIOAction args retProxy
  return $ IOAction (IOActionArg t': args') ret


-- | Examine the action queued to determine if the next entry matches the given signature.
--   If it does, return the cached result instead of executing the function. Otherwise
--   execute the function and return its result in the action history.
doIOAct ::
  forall ret.
  IOActionValue ret =>
  [IOActionArg] ->
  IO ret ->
  IO ret
doIOAct args f = modifyMVar ioActionStore $ \(IOActionStore queued history desync) -> case (queued, desync) of
  (next:rest,False) -> case MP.parseMaybe (parseIOAction args (Proxy @ret)) next of
    Just ioact | ioActionArgs ioact == args -> return $ (IOActionStore rest (Some ioact:history) desync, ioActionRet ioact)
    _ -> do
      ret <- f
      let actualAction = IOAction args ret
      return $ (IOActionStore rest (Some actualAction:history) True, ret)
  -- either desync or no more queued actions, so we execute the function and continue
  (rest,_) -> do
    ret <- f
    let actualAction = IOAction args ret
    return $ (IOActionStore rest (Some actualAction:history) desync, ret)
      
doIOAct1 :: (IOActionValue arg1, IOActionValue ret) =>
  arg1 ->
  IO ret ->
  IO ret
doIOAct1 arg1 f = doIOAct [IOActionArg arg1] f

doIOAct2 :: (IOActionValue arg1, IOActionValue arg2, IOActionValue ret) =>
  arg1 ->
  arg2 ->
  IO ret ->
  IO ret
doIOAct2 arg1 arg2 f = doIOAct [IOActionArg arg1, IOActionArg arg2] f

doIOAct3 :: (IOActionValue arg1, IOActionValue arg2, IOActionValue arg3, IOActionValue ret) =>
  arg1 ->
  arg2 ->
  arg3 ->
  IO ret ->
  IO ret
doIOAct3 arg1 arg2 arg3 f = doIOAct [IOActionArg arg1, IOActionArg arg2, IOActionArg arg3] f