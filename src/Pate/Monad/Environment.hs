{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE PatternSynonyms #-}

module Pate.Monad.Environment (
    EquivEnv(..)
  , envCtxL
  , BlockCache(..)
  , freshBlockCache
  , ExitPairCache
  , NodePriorityK(..)
  , mkPriority
  , normalPriority
  , NodePriority
  , lowerPriority
  , raisePriority
  , printPriorityKind
  , tagPriority
  , priorityTag
  , SolverCacheFrameF(..)
  , SolverCacheFrame
  , SolverCache(..)
  , pattern SolverCacheFrame
  , SolverCacheFrameRef
  , emptyCacheFrame
  , resolveCacheFrameRef
  , diffCacheFrame
  , makeCacheFrameRef
  , unionCacheFrame
  , lookupSolverCache
  , insertSolverCache
  , emptySolverCache
  , lookupSolverCache_
  ) where

import qualified Control.Concurrent as IO
import qualified Control.Concurrent.MVar as MVar
import qualified Control.Lens as L

import           Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as Set
import qualified Data.Time as TM

import qualified Data.Parameterized.Nonce as N
import           Data.Parameterized.Some

import qualified Data.IORef as IO
import qualified Data.Parameterized.SetF as SetF

import qualified Lumberjack as LJ

import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.CFGSlice as MCS
import qualified Data.Macaw.CFG as MC
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Simulator as CS

import qualified What4.Interface as W4

import qualified Pate.Arch as PA
import qualified Pate.AssumptionSet as PAS
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Config as PC
import qualified Pate.Equivalence.Statistics as PES
import qualified Pate.Event as PE
import qualified Pate.Memory.MemTrace as MT
import qualified Pate.Monad.Context as PMC
import qualified Pate.PatchPair as PPa
import qualified Pate.Location as PL
import qualified Pate.Proof as PF
import qualified Pate.Solver as PSo
import qualified Pate.SymbolTable as PSym
import qualified Pate.Verification.Override as PVO
import qualified Pate.Verification.Override.Library as PVOL
import           Pate.TraceTree
import qualified Prettyprinter as PP
import Data.Parameterized.Map (MapF)
import qualified What4.Expr.GroundEval as W4G
import Data.Set (Set)
import Pate.SimState (VarScope, Scoped (..), SimSpec)
import Data.Functor.Identity
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.Map as MapF
import Data.Parameterized.Classes
import Data.Parameterized.WithOrd
import qualified Pate.ExprMappable as PEM
import Control.Monad (forM, foldM)
import Control.Monad.IO.Class

data EquivEnv sym arch where
  EquivEnv ::
    { envWhichBinary :: Maybe (Some PBi.WhichBinaryRepr)
    , envValidArch :: PA.SomeValidArch arch
    , envCtx :: PMC.EquivalenceContext sym arch
    , envArchVals :: MS.GenArchVals MT.MemTraceK arch
    , envLLVMArchVals :: MS.GenArchVals MS.LLVMMemory arch
    , envExtensions :: CS.ExtensionImpl (MS.MacawSimulatorState sym) sym (MS.MacawExt arch)
    , envPCRegion :: W4.SymNat sym
    , envMemTraceVar :: CS.GlobalVar (MT.MemTrace arch)
    , envBlockEndVar :: CS.GlobalVar (MCS.MacawBlockEndType arch)
    -- ^ The global variable used to hold memory for the LLVM memory model while
    -- symbolically executing functions in the "inline callee" feature
    , envLogger :: LJ.LogAction IO (PE.Event arch)
    , envConfig :: PC.VerificationConfig PA.ValidRepr
    -- ^ input equivalence problems to solve
    , envValidSym :: PSo.Sym sym
    -- ^ expression builder, wrapped with a validity proof
    , envStartTime :: TM.UTCTime
    -- ^ start checkpoint for timed events - see 'startTimer' and 'emitEvent'
    , envCurrentFrame :: PAS.AssumptionSet sym
    -- ^ the current assumption frame, accumulated as assumptions are added
    , envPathCondition :: PAS.AssumptionSet sym
    -- ^ assumptions specific to a particular path (subsumed by envCurrentFrame)
    , envNonceGenerator :: N.NonceGenerator IO (PF.SymScope sym)
    , envParentNonce :: Some (PF.ProofNonce sym)
    -- ^ nonce of the parent proof node currently in scope
    , envUndefPointerOps :: MT.UndefinedPtrOps sym
    , envParentBlocks :: [PB.BlockPair arch]
    -- ^ all block pairs on this path from the toplevel
    , envEqCondFns :: Map (PB.FunPair arch) (PL.SomeLocation sym arch -> Bool)
    -- ^ functions that should be considered for generating equivalence conditions
    , envExitPairsCache :: ExitPairCache arch
    -- ^ cache for intermediate proof results
    , envStatistics :: MVar.MVar PES.EquivalenceStatistics
    -- ^ Statistics collected during verification
    , envOverrides :: forall w
                    . (LCLM.HasPtrWidth w, LCLM.HasLLVMAnn sym, ?memOpts :: LCLM.MemOptions, DMM.MemWidth w)
                   => PVOL.OverrideConfig sym w
                   -> M.Map PSym.Symbol (PVO.SomeOverride arch sym)
    -- ^ Overrides to apply in the inline-callee symbolic execution mode
    , envTreeBuilder :: TreeBuilder '(sym, arch)
    , envResetTraceTree :: IO ()
    , envTargetEquivRegs :: Set.Set (Some (MC.ArchReg arch))
    , envPtrAssertions :: MT.PtrAssertions sym
    , envCurrentPriority :: NodePriority
    , envSolverBlockCache :: BlockCache arch (SimSpec sym arch (SolverCache sym))
    -- ^ individual solver cache for each node
    , envInProgressCache :: IO.IORef (Some (SolverCache sym))
    -- ^ the solver cache that's currently under construction (i.e. one a block has been picked)
    , envSolverCache :: SolverCacheFrameRef sym
    -- ^ currently in-scope cache frame
    , envCurrentFramePred :: W4.Pred sym
    } -> EquivEnv sym arch

-- | Scheduling priority for the worklist
data NodePriorityK = 
    PriorityUserRequest
  | PriorityHandleActions
  | PriorityHandleDesync
  | PriorityNodeRecheck
  | PriorityPropagation
  | PriorityWidening
  | PriorityDomainRefresh
  | PriorityHandleReturn
  | PriorityMiscCleanup
  | PriorityDeferred
  deriving (Eq, Ord)

data NodePriority = NodePriority {_priorityK :: NodePriorityK, priorityInt :: Int, priorityTag :: String }
  deriving (Eq, Ord)

printPriorityKind ::
  NodePriority -> String
printPriorityKind (NodePriority pk _ _ ) = case pk of
  PriorityUserRequest -> "User Request"
  PriorityHandleActions -> "Handling Domain Refinements"
  PriorityHandleDesync -> "Handling Control Flow Desynchronization"
  PriorityNodeRecheck -> "Re-checking Block Exits"
  PriorityPropagation -> "Propagating Conditions"
  PriorityWidening -> "Widening Equivalence Domains"
  PriorityDomainRefresh -> "Re-checking Equivalence Domains"
  PriorityHandleReturn -> "Handling Function Return"
  PriorityMiscCleanup -> "Proof Cleanup"
  PriorityDeferred -> "Handling Deferred Decisions"

instance IsTraceNode k "priority" where
  type TraceNodeType k "priority" = NodePriority
  prettyNode () p = 
    (PP.pretty (printPriorityKind p))
    PP.<+> PP.parens (PP.pretty (priorityTag p)) 
    PP.<+> PP.pretty (priorityInt p)

  nodeTags = [(Simplified,\_ -> PP.pretty . printPriorityKind) , (Simplified,\_ -> PP.pretty . printPriorityKind) ]

normalPriority :: NodePriorityK -> NodePriority
normalPriority pk = NodePriority pk 0 ""

mkPriority :: NodePriorityK -> NodePriority -> NodePriority
mkPriority pk (NodePriority _ x msg) = NodePriority pk x msg

tagPriority :: String -> NodePriority -> NodePriority
tagPriority msg (NodePriority pk x _) = NodePriority pk x msg

lowerPriority :: NodePriority -> NodePriority
lowerPriority (NodePriority pK x msg) = (NodePriority pK (x+1) msg)

raisePriority :: NodePriority -> NodePriority
raisePriority (NodePriority pK x msg) = (NodePriority pK (x-1) msg)

-- pushing assumption contexts should:
--    preserve the Unsat cache from the outer context into the inner context
--    (i.e. adding assumptions cannot make an unsatsfiable predicate satisfiable)
--    discard the Sat cache from the outer context
--    (i.e. previously satisfiable predicate may become unsatisfiable with more assumpionts)
-- popping assumption contexts should
--    discard any discovered Unsat results from inner context
--    (i.e. relaxing assumptions may cause previously unsatsfiable results to now be satisfiable)
--    preserve any learned Sat results from inner context
--    (i.e. relaxing assumptions cannot may a satsifiable result unsatisfiable)

type ExitPairCache arch = BlockCache arch (Set.Set (PPa.PatchPair (PB.BlockTarget arch)))

type GroundCache sym = MapF (W4.SymExpr sym) (W4.SymExpr sym)

data SolverCacheFrameF sym f = SolverCacheFrameF
  { unsatCacheF :: f (Set (W4.Pred sym))
  , satCacheF :: f (Set (W4.Pred sym))
  , concCacheF :: f (GroundCache sym)
  , symCacheF :: f (Set (Some (W4.SymExpr sym)))
  }

pattern SolverCacheFrame :: 
  Set (W4.Pred sym) -> Set (W4.Pred sym) -> GroundCache sym -> Set (Some (W4.SymExpr sym)) -> SolverCacheFrameF sym Identity
pattern SolverCacheFrame a b c d = SolverCacheFrameF (Identity a) (Identity b) (Identity c) (Identity d)
{-# COMPLETE SolverCacheFrame #-}

type SolverCacheFrame sym = SolverCacheFrameF sym Identity
type SolverCacheFrameRef sym = SolverCacheFrameF sym IO.IORef

emptyCacheFrame :: SolverCacheFrame sym
emptyCacheFrame = SolverCacheFrame Set.empty Set.empty MapF.empty Set.empty

emptySolverCache :: SolverCache sym v
emptySolverCache = SolverCache M.empty

resolveCacheFrameRef :: SolverCacheFrameRef sym -> IO (SolverCacheFrame sym)
resolveCacheFrameRef sc = TF.traverseF (\x -> Identity <$> IO.readIORef x) sc

makeCacheFrameRef :: SolverCacheFrame sym -> IO (SolverCacheFrameRef sym)
makeCacheFrameRef sc = TF.traverseF (\(Identity x) -> IO.newIORef x) sc

-- | Reduce the first cache frame to only have elements that are not in the second
diffCacheFrame :: forall sym.
  OrdF (W4.SymExpr sym) => SolverCacheFrame sym -> SolverCacheFrame sym -> SolverCacheFrame sym
diffCacheFrame (SolverCacheFrame unsatL satL concL symL) (SolverCacheFrame unsatR satR concR symR) =
  withOrd @(W4.SymExpr sym) @W4.BaseBoolType $
  SolverCacheFrame (Set.difference unsatL unsatR) (Set.difference satL satR) 
    (MapF.filterWithKey (\k _ -> not (MapF.member k concR)) concL)
    (Set.difference symL symR)

unionCacheFrame :: forall sym.
  OrdF (W4.SymExpr sym) => SolverCacheFrame sym -> SolverCacheFrame sym -> Either String (SolverCacheFrame sym)
unionCacheFrame (SolverCacheFrame unsatL satL concL symL) (SolverCacheFrame unsatR satR concR symR) =
  withOrd @(W4.SymExpr sym) @W4.BaseBoolType $
  SolverCacheFrame <$> pure (Set.union unsatL unsatR) <*> pure (Set.union satL satR) <*>
    (MapF.mergeWithKeyM (\_k e1 e2 -> case testEquality e1 e2 of Just Refl -> return (Just e1); _ -> Left "unionCacheFrame: mismatch")
      pure pure concL concR) <*> pure (Set.union symL symR)

instance TF.FunctorF (SolverCacheFrameF sym) where
  fmapF = TF.fmapFDefault

instance TF.FoldableF (SolverCacheFrameF sym) where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF (SolverCacheFrameF sym) where
  traverseF f (SolverCacheFrameF a b c d) = SolverCacheFrameF <$> (f a) <*> (f b) <*> (f c) <*> (f d)

newtype SolverCache sym (v :: VarScope) = 
  SolverCache (Map (W4.Pred sym) (SolverCacheFrame sym))

instance PEM.ExprMappable sym (SolverCacheFrameF sym Identity) where
  mapExpr _sym f (SolverCacheFrame a b c d) = withOrd @(W4.SymExpr sym) @W4.BaseBoolType $ do
    a' <- Set.fromList <$> mapM f (Set.toList a)
    b' <- Set.fromList <$> mapM f (Set.toList b)
    -- Note: this will drop duplicate entries if there are clashing keys
    -- in the resulting map
    c' <- fmap (MapF.fromList) $ forM (MapF.toList c) $ \(MapF.Pair k v) -> do
      k' <- f k
      v' <- f v
      return $ MapF.Pair k' v'
    d' <- mapM (\(Some e) -> do
      e' <- f e
      liftIO $ putStrLn $ "Old:  \n" ++ show (W4.printSymExpr e) ++ "\n" ++ show (hashF e) ++ "\nNew\n" ++ show (W4.printSymExpr e') ++ "\n" ++ show (hashF e') 
      Some <$> return e') (Set.toList d)
    d'' <- foldM (\acc (Some e) -> case Set.lookupIndex (Some e) acc of
      Just i -> do
        (Some e') <- return $ Set.elemAt i acc
        -- liftIO $ putStrLn $ "Duplicate dropped:  \n" ++ show (W4.printSymExpr e) ++ "\n" ++ show (hashF e) ++ "\n" ++ show (W4.printSymExpr e') ++ "\n" ++ show (hashF e') 
        
        return acc
      Nothing -> return $ Set.insert (Some e) acc
      ) Set.empty d'
    return $ SolverCacheFrame a' b' c' d''

instance PEM.ExprMappable sym (SolverCache sym v) where
  -- Note: this will drop duplicate entries if there are clashing keys
  -- in the resulting map
  -- We could consider merging the caches instead, but this is unlikely to
  -- happen in practice, since we are just using this to rewrite
  -- the bound variables
  mapExpr sym f (SolverCache m) = 
    withOrd @(W4.SymExpr sym) @W4.BaseBoolType $ 
    fmap (SolverCache . M.fromList) $ forM (M.toList m) $ \(k,v) -> do
      k' <- f k
      v' <- PEM.mapExpr sym f v
      return (k', v')


lookupSolverCache ::
  forall sym v.
  OrdF (W4.SymExpr sym) => 
  W4.Pred sym ->
  SolverCache sym v ->
  SolverCacheFrame sym
lookupSolverCache p (SolverCache m) = withOrd @(W4.SymExpr sym) @W4.BaseBoolType $ 
  case M.lookup p m of
    Just sc -> sc
    Nothing -> emptyCacheFrame

lookupSolverCache_ ::
  forall sym v.
  OrdF (W4.SymExpr sym) => 
  W4.Pred sym ->
  SolverCache sym v ->
  Maybe (SolverCacheFrame sym)
lookupSolverCache_ p (SolverCache m) =
  withOrd @(W4.SymExpr sym) @W4.BaseBoolType $ M.lookup p m

insertSolverCache ::
  forall sym v.
  OrdF (W4.SymExpr sym) => 
  W4.Pred sym ->
  SolverCacheFrame sym ->
  SolverCache sym v ->
  SolverCache sym v
insertSolverCache p sc (SolverCache m) = withOrd @(W4.SymExpr sym) @W4.BaseBoolType $ 
  SolverCache $ M.insert p sc m

instance Scoped (SolverCache sym) where
  unsafeCoerceScope (SolverCache m) = SolverCache m 

data BlockCache arch a where
  BlockCache :: IO.MVar (Map (PB.BlockPair arch) a) -> BlockCache arch a

envCtxL :: L.Lens' (EquivEnv sym arch) (PMC.EquivalenceContext sym arch)
envCtxL f ee = fmap (\c' -> ee { envCtx = c' }) (f (envCtx ee))

freshBlockCache ::
  IO (BlockCache arch a)
freshBlockCache = BlockCache <$> IO.newMVar M.empty
