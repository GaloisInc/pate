{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE DataKinds   #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}

module What4.Simplify (
   SimpCheck(..)
 , noSimpCheck
 , unliftSimpCheck
 , runSimpCheck
 , runSimpCheckTrace
 , wrapSimpSolverCheck
 , SimpT
 , simpLog
 , simpCheck
 , simpCheckTraced
 , runSimpT
 , simpMaybe
 , withSym
 , appAlts
 , asApp
 , tryAll
 , Simplifier(..)
 , SimpStrategy(..)
 , mkSimpleStrategy
 , joinStrategy
 , mkSimplifier
 , simplifyGenApp
 , simplifyApp
 , genAppSimplifier
 , liftSimpTGenStrategy
 , liftSimpTStrategy
 , setProgramLoc
) where

import           Control.Applicative
import           Control.Monad
import qualified Control.Monad.IO.Class as IO
import           Control.Monad.IO.Class (liftIO)
import qualified Control.Monad.IO.Unlift as IO
import qualified Control.Monad.Trans.Reader as RWS hiding (ask, local)
import qualified Control.Monad.Reader as RWS
import           Control.Monad.Trans.Maybe (MaybeT(..))
import           Control.Monad.Trans (MonadTrans(..))

import           Data.Parameterized.Classes
import qualified Data.Parameterized.TraversableFC as TFC

import qualified What4.Expr.Builder as W4B
import qualified What4.Interface as W4
import qualified What4.Expr.GroundEval as W4G
import qualified What4.ProgramLoc as W4PL


-- | An action for validating a simplification step.
-- After a step is taken, this function is given the original expression as the
-- first argument and the simplified expression as the second argument.
-- This action should check that the original and simplified expressions are equal,
-- and return the simplified expression if they are, or the original expression if they are not,
-- optionally raising any exceptions or warnings in the given monad.
data SimpCheck sym m = SimpCheck
  { simpCheckLog :: String -> m ()
  , runSimpCheck_ :: forall tp. 
      (forall t fs solver. 
      sym ~ W4B.ExprBuilder t solver fs => W4G.GroundEvalFn t -> m ()) ->
      W4.SymExpr sym tp -> 
      W4.SymExpr sym tp -> 
      m (W4.SymExpr sym tp) 
  }

instance Monad m => Monoid (SimpCheck sym m) where
  mempty = noSimpCheck

instance Monad m => Semigroup (SimpCheck sym m) where
  (SimpCheck l1 f1) <> (SimpCheck l2 f2) = SimpCheck (\msg -> l1 msg >> l2 msg) 
    (\cet e_orig e_simp -> f1 cet e_orig e_simp >>= \e_simp' -> f2 cet e_orig e_simp')

noSimpCheck :: Applicative m => SimpCheck sym m
noSimpCheck = SimpCheck (\_ -> pure ()) (\_ _ -> pure)

unliftSimpCheck :: IO.MonadUnliftIO m => SimpCheck sym m -> m (SimpCheck sym IO)
unliftSimpCheck simp_check = IO.withRunInIO $ \inIO -> do
  return $ SimpCheck (\msg -> inIO (simpCheckLog simp_check msg)) (\ce e1 e2 -> inIO (runSimpCheck_ simp_check ((\x -> IO.liftIO $ ce x)) e1 e2))


runSimpCheck :: Monad m => SimpCheck sym m -> W4.SymExpr sym tp -> W4.SymExpr sym tp -> m (W4.SymExpr sym tp)
runSimpCheck simp_check = runSimpCheck_ simp_check (\_ -> pure ())

runSimpCheckTrace :: 
  Monad m => 
  SimpCheck sym m ->
  (forall t fs solver. 
        sym ~ W4B.ExprBuilder t solver fs => W4G.GroundEvalFn t -> m ()) ->
  W4.SymExpr sym tp -> W4.SymExpr sym tp -> m (W4.SymExpr sym tp)
runSimpCheckTrace simp_check f = runSimpCheck_ simp_check f


-- | Add a pre-processing step before sending to the solver.
--   This step is assumed to produce an equivalent term, but its
--   result is discarded in the final output.
wrapSimpSolverCheck ::
  Monad m =>
  W4.IsSymExprBuilder sym =>
  (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) ->
  SimpCheck sym m ->
  SimpCheck sym m
wrapSimpSolverCheck f (SimpCheck l r) = SimpCheck l $ \tr e_orig e_simp -> do
  e_orig' <- f e_orig
  e_simp' <- f e_simp
  e_simp'' <- r tr e_orig' e_simp'
  case testEquality e_simp'' e_simp' of
    Just Refl -> return e_simp
    Nothing -> return e_orig

data Sym sym where
  Sym :: (W4B.ExprBuilder t solver fs) -> Sym (W4B.ExprBuilder t solver fs)

newtype SimpT sym m a = SimpT { _unSimpT :: MaybeT (RWS.ReaderT (Sym sym, SimpCheck sym m) m) a }
  deriving (Functor, Applicative, Alternative, MonadPlus, Monad, RWS.MonadReader (Sym sym, SimpCheck sym m), IO.MonadIO)

instance Monad m => MonadFail (SimpT sym m) where
  fail msg = do
    simpLog ("Failed: " ++ msg)
    SimpT $ fail msg

instance MonadTrans (SimpT sym) where
  lift f = SimpT $ lift $ lift f

runSimpT ::
  Monad m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  SimpCheck sym m -> 
  SimpT sym m a -> m (Maybe a)
runSimpT sym simp_check (SimpT f) = RWS.runReaderT (runMaybeT f) (Sym sym, simp_check)

simpMaybe :: Monad m => Maybe a -> SimpT sym m a
simpMaybe (Just a) = return a
simpMaybe Nothing = fail ""

withSym :: Monad m => (forall t solver fs. sym ~ (W4B.ExprBuilder t solver fs) => sym -> SimpT sym m a) -> SimpT sym m a
withSym f = do
  (Sym sym, _) <- RWS.ask
  f sym

appAlts :: W4B.App (W4.SymExpr sym) tp -> [W4B.App (W4.SymExpr sym) tp]
appAlts app = [app] ++ case app of
  W4B.BaseEq r e1 e2 -> [W4B.BaseEq r e2 e1]
  _ -> []

asApp :: Monad m => W4.SymExpr sym tp -> SimpT sym m (W4B.App (W4.SymExpr sym) tp) 
asApp e = withSym $ \_ -> simpMaybe $ W4B.asApp e


tryAll :: Alternative m => [a] -> (a -> m b) -> m b
tryAll (a : as) f = f a <|> tryAll as f
tryAll [] _f = empty

simpLog :: Monad m => String -> SimpT sym m ()
simpLog msg = do
 (_, simp_check) <- RWS.ask
 lift $ simpCheckLog simp_check msg

simpCheck :: Monad m => W4.SymExpr sym tp -> W4.SymExpr sym tp -> SimpT sym m (W4.SymExpr sym tp)
simpCheck orig_expr simp_expr = do
 (_, simp_check) <- RWS.ask
 lift $ runSimpCheck simp_check orig_expr simp_expr

simpCheckTraced :: Monad m =>
  W4.SymExpr sym tp -> W4.SymExpr sym tp -> 
  (forall t fs solver. 
      sym ~ W4B.ExprBuilder t solver fs => W4G.GroundEvalFn t -> m ()) ->  
  SimpT sym m (W4.SymExpr sym tp)
simpCheckTraced orig_expr simp_expr tr = do
 (_, simp_check) <- RWS.ask
 lift $ runSimpCheckTrace simp_check tr orig_expr simp_expr

-- | A thin wrapper around a monadic expression ('W4.SymExpr') transformer.
data Simplifier sym m =
   Simplifier { runSimplifier :: forall tp. W4.SymExpr sym tp -> m (W4.SymExpr sym tp) }

instance Monad m => Monoid (Simplifier sym m) where
  mempty = Simplifier pure

instance Monad m => Semigroup (Simplifier sym m) where
  (Simplifier f1) <> (Simplifier f2) = Simplifier $ \e -> f1 e >>= f2

-- | A 'SimpStrategy' is a function that produces a 'Simplifier' in the given
-- monad 'm'. This allows the strategy to first perform any required initialization
-- (e.g. creating fresh term caches) before it is applied. Subsequent applications
-- of the resulting 'Simplifier' will then re-use the initialized data (e.g. using
-- cached results).
-- Importantly, in composite strategies all initialization occurs before any
-- simplification.
data SimpStrategy sym m where
    SimpStrategy :: 
      { getStrategy :: 
        sym ->
        SimpCheck sym m -> 
        m (Simplifier sym m)
      } -> SimpStrategy sym m

instance Monad m => Monoid (SimpStrategy sym m) where
  mempty = SimpStrategy (\_ _ -> return mempty)

instance Monad m => Semigroup (SimpStrategy sym m) where
  (SimpStrategy f1) <> (SimpStrategy f2) = SimpStrategy $ \sym check -> do
    simp_f1 <- f1 sym check
    simp_f2 <- f2 sym check
    return $ simp_f1 <> simp_f2

mkSimpleStrategy ::
  forall sym m.
  Monad m =>
  (forall tp. sym -> W4.SymExpr sym tp -> m (W4.SymExpr sym tp)) -> SimpStrategy sym m
mkSimpleStrategy f = SimpStrategy $ \sym _ -> return $ Simplifier $ \e -> f sym e

joinStrategy ::
  Monad m =>
  m (SimpStrategy sym m) -> 
  SimpStrategy sym m
joinStrategy f = SimpStrategy $ \sym check -> do
  strat <- f
  getStrategy strat sym check

mkSimplifier :: 
  Monad m =>
  sym -> 
  SimpCheck sym m -> 
  SimpStrategy sym m -> 
  m (Simplifier sym m)
mkSimplifier sym simp_check strat = do
  Simplifier strat' <- getStrategy strat sym simp_check
  return $ Simplifier strat'

setProgramLoc ::
  forall m sym t solver fs tp.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4.SymExpr sym tp ->
  m ()
setProgramLoc sym e = case W4PL.plSourceLoc (W4B.exprLoc e) of
  W4PL.InternalPos -> return ()
  _ -> liftIO $ W4.setCurrentProgramLoc sym (W4B.exprLoc e)

--   Create a 'Simplifier' that recurses into the sub-term structure of
--   expressions using the given 'W4B.App' and 'W4B.NonceApp' transformers.
--   For each subterm 'e', if the corresponding 'SimpT' operation succeeds
--   the result is used (i.e. replaced in the term) without further simplification. Otherwise, the simplification
--   traverses further into the sub-terms of 'e'.
--   The given operations are therefore responsible for handling any recursive
--   application of this simplification.
--   See 'liftSimpTGenStrategy', where each transformer is passed a recursor function.
genAppSimplifier ::
  forall sym m t solver fs.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4B.IdxCache t (W4B.Expr t) ->
  SimpCheck sym m ->
  (forall tp'. W4B.App (W4B.Expr t) tp' -> SimpT sym m (W4.SymExpr sym tp')) {- ^ app simplification -} ->
  (forall tp'. W4B.NonceApp t (W4B.Expr t) tp' -> SimpT sym m (W4.SymExpr sym tp')) {- ^ nonce app simplification -} ->
  Simplifier sym m
genAppSimplifier sym cache simp_check simp_app simp_nonce_app =
  let
    else_ :: forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')
    else_ e = do
      e' <- case e of
        W4B.AppExpr a0 -> do
          a0' <- W4B.traverseApp go (W4B.appExprApp a0)
          if (W4B.appExprApp a0) == a0' then return e
          else (liftIO $ W4B.sbMakeExpr sym a0') >>= go
        W4B.NonceAppExpr a0 -> do
          a0' <- TFC.traverseFC go (W4B.nonceExprApp a0)
          if (W4B.nonceExprApp a0) == a0' then return e
          else (liftIO $ W4B.sbNonceExpr sym a0') >>= go
        _ -> return e
      runSimpCheck simp_check e e'

    go :: forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')
    go e = W4B.idxCacheEval cache e $ do
      setProgramLoc sym e
      case e of
        W4B.AppExpr a0 -> runSimpT sym simp_check (simp_app (W4B.appExprApp a0))  >>= \case
          Just e' -> runSimpCheck simp_check e e'
          Nothing -> else_ e
        W4B.NonceAppExpr a0 -> runSimpT sym simp_check (simp_nonce_app (W4B.nonceExprApp a0)) >>= \case
          Just e' -> runSimpCheck simp_check e e'
          Nothing -> else_ e
        _ -> else_ e
  in Simplifier go

simplifyGenApp ::
  forall sym m t solver fs tp.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4B.IdxCache t (W4B.Expr t) ->
  SimpCheck sym m {- ^ double-check simplification step -} ->
  (forall tp'. W4B.App (W4B.Expr t) tp' -> m (Maybe (W4.SymExpr sym tp'))) {- ^ app simplification -} ->
  (forall tp'. W4B.NonceApp t (W4B.Expr t) tp' -> m (Maybe (W4.SymExpr sym tp'))) {- ^ nonce app simplification -} ->
  W4.SymExpr sym tp ->
  m (W4.SymExpr sym tp)
simplifyGenApp sym cache check f_app f_nonce_app e = do
  let s = genAppSimplifier sym cache check (\app -> simpMaybe =<< lift (f_app app)) (\nonce_app -> simpMaybe =<< lift (f_nonce_app nonce_app))
  runSimplifier s e

simplifyApp ::
  forall sym m t solver fs tp.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  sym ->
  W4B.IdxCache t (W4B.Expr t) ->
  SimpCheck sym m {- ^ double-check simplification step -} ->
  (forall tp'. W4B.App (W4B.Expr t) tp' -> m (Maybe (W4.SymExpr sym tp'))) {- ^ app simplification -} ->
  W4.SymExpr sym tp ->
  m (W4.SymExpr sym tp)
simplifyApp sym cache simp_check simp_app e = simplifyGenApp sym cache simp_check simp_app (\_ -> return Nothing) e


-- | Lift a pair of 'W4B.App' and 'W4B.NonceApp' transformers into a 'SimpStrategy' by recursively applying them
--   to the sub-terms of an expression. For each subterm 'e', if the corresponding 'SimpT' operation succeeds
--   the result is used without further simplification. Otherwise, the simplification
--   traverses further into the sub-terms of 'e'.
--   The first argument to the given function is the recursive application of this
--   strategy, which can be used to selectively simplify sub-terms during transformation.
liftSimpTGenStrategy ::
  forall m sym t solver fs.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  (forall tp''. (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) -> 
   W4B.App (W4.SymExpr sym) tp'' -> SimpT sym m (W4.SymExpr sym tp'')) ->
  (forall tp''. (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) -> 
   W4B.NonceApp t (W4B.Expr t) tp'' -> SimpT sym m (W4.SymExpr sym tp'')) ->
  SimpStrategy sym m
liftSimpTGenStrategy f_app f_nonce_app = SimpStrategy $ \sym check -> do
  cache <- W4B.newIdxCache
  let
    go :: Simplifier sym m
    go = genAppSimplifier sym cache check (\app -> f_app (\e' -> runSimplifier go e') app) (\nonce_app -> f_nonce_app (\e' -> runSimplifier go e') nonce_app)
  return go

-- | Specialized form of 'liftSimpTGenStrategy' that only takes an 'W4B.App' transformer.
liftSimpTStrategy :: 
  forall m sym t solver fs.
  IO.MonadIO m =>
  sym ~ (W4B.ExprBuilder t solver fs) =>
  (forall tp''. (forall tp'. W4.SymExpr sym tp' -> m (W4.SymExpr sym tp')) -> 
   W4B.App (W4.SymExpr sym) tp'' -> SimpT sym m (W4.SymExpr sym tp'')) ->
  SimpStrategy sym m
liftSimpTStrategy f_app = liftSimpTGenStrategy f_app (\_ _ -> fail "")