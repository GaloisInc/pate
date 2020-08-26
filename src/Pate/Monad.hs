{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}

module Pate.Monad
  ( EquivEnv(..)
  , EquivM
  , EquivM_
  , runEquivM
  , ValidSym
  , ValidSolver
  , ValidArch
  , EquivalenceContext(..)
  , BinaryContext(..)
  , withValid
  , withSymIO
  , withProc
  , withArchVals
  , withArchFuns
  , runInIO1
  , errorFrame
  , manifestError
  , implicitError
  )
  where

import           Prelude hiding ( fail )
import           GHC.Stack

import           Control.Monad.Fail
import qualified Control.Monad.IO.Unlift as IO
import           Control.Exception
import           Control.Monad.ST
import           Control.Monad.Trans.Reader ( ReaderT, runReaderT )
import           Control.Monad.Reader
import           Control.Monad.Trans.Except
import           Control.Monad.Except

import           Data.Typeable
import qualified Data.ElfEdit as E

import qualified Data.Parameterized.Nonce as N

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.GlobalState as CGS
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as CLM

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.MemTraceOps as MT

import qualified What4.Interface as W4
import qualified What4.Protocol.Online as W4O
import qualified What4.Protocol.SMTWriter as W4W

import           Pate.Types


data BinaryContext sym arch = BinaryContext
  { binary :: MBL.LoadedBinary arch (E.Elf (MM.ArchAddrWidth arch))
  , extensions :: CS.ExtensionImpl (MS.MacawSimulatorState sym) sym (MS.MacawExt arch)
  , globalMap :: CGS.SymGlobalState sym
  , parsedFunctionMap :: ParsedFunctionMap arch
  }

data EquivalenceContext sym ids arch where
  EquivalenceContext ::
    forall sym ids arch scope solver fs.
    (ValidArch arch, ValidSym sym, ValidSolver sym scope solver fs) =>
    { nonces :: N.NonceGenerator (ST RealWorld) ids
    , handles :: CFH.HandleAllocator
    , archVals :: MS.ArchVals arch
    , exprBuilder :: sym
    , memTraceVar :: CS.GlobalVar (MT.MemTrace arch)
    , ipEquivalence :: CLM.LLVMPtr sym (MM.ArchAddrWidth arch) -> CLM.LLVMPtr sym (MM.ArchAddrWidth arch) -> IO (W4.Pred sym)
    , originalCtx :: BinaryContext sym arch
    , rewrittenCtx :: BinaryContext sym arch
    } -> EquivalenceContext sym ids arch

type ValidArch arch =
  ( Typeable arch
  , MBL.BinaryLoader arch (E.Elf (MM.ArchAddrWidth arch))
  , MS.SymArchConstraints arch
  )


type ValidSym sym =
  ( W4.IsExprBuilder sym
  , CB.IsSymInterface sym
  )

type ValidSolver sym scope solver fs =
  (sym ~ CBO.OnlineBackend scope solver fs
  , W4O.OnlineSolver solver
  , W4W.SMTReadWriter solver
  )

data EquivEnv sym arch where
  EquivEnv ::
    forall sym arch scope solver fs.
    (ValidArch arch, ValidSym sym, ValidSolver sym scope solver fs) =>
    { envSym :: sym
    , envProc :: W4O.SolverProcess scope solver
    } -> EquivEnv sym arch


newtype EquivM_ sym arch a = EquivM { unEQ :: ReaderT (EquivEnv sym arch) (ExceptT (EquivalenceError arch) IO) a }
  deriving (Functor
           , Applicative
           , Monad
           , IO.MonadIO
           , MonadReader (EquivEnv sym arch)
           , MonadError (EquivalenceError arch)
           )

type EquivM sym arch a = (ValidArch arch, ValidSym sym) => EquivM_ sym arch a

withValid ::
  (forall scope solver fs.
    ValidSolver sym scope solver fs =>
    EquivM sym arch a) ->
  EquivM_ sym arch a
withValid f = do
  env <- ask
  withValidEnv env $ f

withValidEnv ::
  EquivEnv sym arch ->
  (forall scope solver fs.
    ValidArch arch =>
    ValidSym sym =>
    ValidSolver sym scope solver fs =>
    a) ->
  a
withValidEnv (EquivEnv {}) f = f

withSym ::
  ( forall scope solver fs.
    ValidSolver sym scope solver fs =>
    sym ->
   EquivM sym arch a) ->
  EquivM sym arch a
withSym f = withValid $ do
  sym <- asks envSym
  f sym

withProc ::
  ( forall scope solver fs.
    ValidSolver sym scope solver fs =>
    W4O.SolverProcess scope solver ->
   EquivM sym arch a) ->
  EquivM sym arch a
withProc f = withValid $ do
  EquivEnv { envProc = p } <- ask
  f p

withSymIO ::
  ( forall scope solver fs.
    sym ~ CBO.OnlineBackend scope solver fs =>
    W4O.OnlineSolver solver =>
    ValidArch arch =>
    ValidSym sym =>
    sym ->
   IO a ) ->
  EquivM sym arch a
withSymIO f = withSym (\sym -> liftIO (f sym))

withArchVals :: forall sym arch a.
  (MS.ArchVals arch -> EquivM sym arch a) ->
  EquivM sym arch a
withArchVals f = do
  Just archVs <- return $ MS.archVals (Proxy @arch)
  f archVs

withArchFuns :: forall sym arch a.
  (MS.MacawSymbolicArchFunctions arch -> EquivM sym arch a) ->
  EquivM sym arch a
withArchFuns f = withArchVals (\archVs -> f (MS.archFunctions archVs))

instance IO.MonadUnliftIO (EquivM_ sym arch) where
  withRunInIO f = withValid $ do
    env <- ask
    (liftIO $ catch (Right <$> f (runEquivM' env)) (\(e :: EquivalenceError arch) -> return $ Left e)) >>= \case
      Left err -> throwError err
      Right result -> return result

runInIO1 :: IO.MonadUnliftIO m => (a -> m b) -> ((a -> IO b) -> IO b) -> m b
runInIO1 f g = do
  IO.UnliftIO outer_io_ctx <- IO.askUnliftIO
  liftIO $ g (\a -> outer_io_ctx (f a))

runEquivM' ::
  EquivEnv sym arch ->
  EquivM sym arch a ->
  IO a
runEquivM' env f = withValidEnv env $ (runExceptT $ runReaderT (unEQ f) env) >>= \case
  Left err -> throwIO err
  Right result -> return $ result

runEquivM ::
  EquivEnv sym arch ->
  EquivM sym arch a ->
  ExceptT (EquivalenceError arch) IO a
runEquivM env f = withValidEnv env $ runReaderT (unEQ f) env

errorHere ::
  HasCallStack =>
  String ->
  EquivM_ sym arch a
errorHere msg = do
  let (_, src): _ = getCallStack callStack
  let msg' = "Error Message: " ++ msg ++ " at: " ++ prettySrcLoc src
  throwError $ EquivalenceError msg'

instance MonadFail (EquivM_ sym arch) where
  fail msg = errorHere $ "Fail: " ++ msg





-- | Wrap the argument in an assumption frame in a way that's safe even if it
-- throws an error.
errorFrame :: (MonadError e m, MonadIO m, CB.IsBoolSolver sym) => sym -> m a -> m a
errorFrame sym act = do
  frame <- liftIO $ CB.pushAssumptionFrame sym
  res <- manifestError act
  _ <- liftIO $ CB.popAssumptionFrame sym frame
  implicitError res

manifestError :: MonadError e m => m a -> m (Either e a)
manifestError act = catchError (Right <$> act) (pure . Left)

implicitError :: MonadError e m => Either e a -> m a
implicitError (Left e) = throwError e
implicitError (Right a) = pure a
