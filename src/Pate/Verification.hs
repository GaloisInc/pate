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
{-# LANGUAGE UndecidableInstances #-}

-- must come after TypeFamilies, see also https://gitlab.haskell.org/ghc/ghc/issues/18006
{-# LANGUAGE NoMonoLocalBinds #-}

module Pate.Verification
  ( verifyPairs
  , EquivalenceError(..)
  , checkRenEquivalence
  , mkIPEquivalence
  , EquivalenceContext(..)
  , EquivalenceStatistics(..)
  ) where

import           Prelude hiding ( fail )

import           Control.Monad.Fail
import           GHC.Stack
import           Data.Typeable

import           Control.Monad.Trans.Reader ( ReaderT, runReaderT )
import           Control.Monad.Trans.Except
import           Control.Monad.Reader
import           Control.Exception

import           Control.Monad.Except
import qualified Control.Monad.IO.Unlift as IO
import           Control.Monad.IO.Class ( liftIO )
import           Control.Applicative
import           Control.Lens hiding ( op, pre )
import           Control.Monad.ST
import qualified Data.BitVector.Sized as BVS
import           Data.Foldable
import           Data.Functor.Compose
import           Data.IntervalMap (IntervalMap)
import qualified Data.IntervalMap as IM
import           Data.List
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Monoid
import           Data.Sequence (Seq)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.String
import           Data.Type.Equality (testEquality)
import           GHC.TypeLits
import           Numeric
import           Numeric.Natural
import           System.IO
import           Unsafe.Coerce

import qualified Data.ElfEdit as E
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.PPC as MP
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.MemTraceOps as MT
import qualified Data.Parameterized.Context.Unsafe as Ctx
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Nonce as N
import qualified Data.Parameterized.Some as S
import qualified Data.Parameterized.TraversableFC as TFC
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.GlobalState as CGS
import qualified Renovate.Arch.PPC as RP
import qualified Renovate as R
import qualified What4.Expr.Builder as W4B
import qualified What4.Expr.GroundEval as W4G
import qualified What4.Interface as W4
import qualified What4.ProblemFeatures as W4PF
import qualified What4.ProgramLoc as W4L
import qualified What4.Protocol.Online as W4O
import qualified What4.Protocol.SMTWriter as W4W
import qualified What4.SatResult as W4R
import qualified What4.Symbol as W4S

data WhichBinary = Original | Rewritten deriving (Bounded, Enum, Eq, Ord, Read, Show)

data EquivalenceError arch
  = BytesNotConsumed { disassemblyAddr :: R.ConcreteAddress arch, bytesRequested :: Int, bytesDisassembled :: Int }
  | AddressOutOfRange { disassemblyAddr :: R.ConcreteAddress arch }
  | UnsupportedArchitecture
  | InvalidRegisterName String W4S.SolverSymbolError
  | UnsupportedRegisterType (S.Some CC.TypeRepr)
  | SymbolicExecutionFailed String -- TODO: do something better
  | InconclusiveSAT
  | IllegalIP String (R.ConcreteAddress arch)
  | BadSolverSymbol String W4S.SolverSymbolError
  | EmptyDisassembly
  | NoUniqueFunctionOwner (IM.Interval (R.ConcreteAddress arch)) [MM.ArchSegmentOff arch]
  | StrangeBlockAddress (MM.ArchSegmentOff arch)
  -- starting address of the block, then a starting and ending address bracketing a range of undiscovered instructions
  | UndiscoveredBlockPart WhichBinary (R.ConcreteAddress arch) (R.ConcreteAddress arch) (R.ConcreteAddress arch)
  | NonConcreteParsedBlockAddress WhichBinary (MM.ArchSegmentOff arch)
  | BlockExceedsItsSegment WhichBinary (MM.ArchSegmentOff arch) (MM.ArchAddrWord arch)
  | BlockEndsMidInstruction WhichBinary
  | PrunedBlockIsEmpty
  | EquivalenceError String -- generic error
deriving instance MM.MemWidth (MM.ArchAddrWidth arch) => Show (EquivalenceError arch)

instance ValidArch arch => Exception (EquivalenceError arch)


data BinaryContext sym arch = BinaryContext
  { binary :: MBL.LoadedBinary arch (E.Elf (MM.ArchAddrWidth arch))
  , extensions :: CS.ExtensionImpl (MS.MacawSimulatorState sym) sym (MS.MacawExt arch)
  , globalMap :: CGS.SymGlobalState sym
  , parsedFunctionMap :: ParsedFunctionMap arch
  }

data EquivalenceContext sym ids arch where
  EquivalenceContext :: (ValidArch arch, ValidSym sym) =>
    { nonces :: N.NonceGenerator (ST RealWorld) ids
    , handles :: CFH.HandleAllocator
    , archVals :: MS.ArchVals arch
    , exprBuilder :: ValidOnlineBackend sym
    , memTraceVar :: CS.GlobalVar (MT.MemTrace arch)
    , ipEquivalence :: CLM.LLVMPtr sym (MM.ArchAddrWidth arch) -> CLM.LLVMPtr sym (MM.ArchAddrWidth arch) -> IO (W4.Pred sym)

    } -> EquivalenceContext sym ids arch

type ValidArch arch =
  (arch ~ RP.PPC64, Typeable arch, (KnownNat (MM.ArchAddrWidth arch), 1 <= MM.ArchAddrWidth arch))


type ValidSym sym = (W4.IsExprBuilder sym, CB.IsSymInterface sym)
type ValidSolver sym scope solver fs =
  (sym ~ CBO.OnlineBackend scope solver fs
  , W4O.OnlineSolver solver
  , W4W.SMTReadWriter solver
  )

data ValidOnlineBackend sym where
  ValidOnlineBackend ::
    ( ValidSolver sym scope solver fs
    , ValidSym sym
    ) => 
    sym ->
    W4O.SolverProcess scope solver ->
    ValidOnlineBackend sym

data EquivEnv sym arch where
  EquivEnv :: ValidArch arch =>
    { originalCtx :: BinaryContext sym arch
    , rewrittenCtx :: BinaryContext sym arch
    , envSymProc :: ValidOnlineBackend sym
    } -> EquivEnv sym arch


newtype EquivM sym arch a = EquivM { _unEQ :: ReaderT (EquivEnv sym arch) (ExceptT (EquivalenceError arch) IO) a }
  deriving (Functor
           , Applicative
           , Monad
           , IO.MonadIO
           , MonadReader (EquivEnv sym arch)
           , MonadError (EquivalenceError arch)
           )

withValid ::
  (forall scope solver fs.
    ValidArch arch =>
    ValidSym sym =>
    ValidSolver sym scope solver fs =>
    EquivM sym arch a) ->
  EquivM sym arch a
withValid f = do
  env <- ask
  withValidEnv env $ f

withValidIO ::
  (forall scope solver fs.
    ValidArch arch =>
    ValidSym sym =>
    ValidSolver sym scope solver fs =>
    IO a) ->
  EquivM sym arch a
withValidIO f = withValid (liftIO f)

withValidEnv ::
  EquivEnv sym arch ->
  (forall scope solver fs.
    ValidArch arch =>
    ValidSym sym =>
    ValidSolver sym scope solver fs =>
    a) ->
  a
withValidEnv (EquivEnv _ _ (ValidOnlineBackend _ _)) f = f

withSym ::
  ( forall scope solver fs.
    ValidSolver sym scope solver fs =>
    ValidArch arch =>
    ValidSym sym =>
    sym ->
   EquivM sym arch a) ->
  EquivM sym arch a
withSym f = withValid $ do
  ValidOnlineBackend sym _ <- asks envSymProc
  f sym

withProc ::
  ( forall scope solver fs.
    ValidSolver sym scope solver fs =>
    ValidSym sym =>
    ValidArch arch =>
    W4O.SolverProcess scope solver ->
   EquivM sym arch a) ->
  EquivM sym arch a
withProc f = withValid $ do
  ValidOnlineBackend _ p <- asks envSymProc
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

instance IO.MonadUnliftIO (EquivM sym arch) where
  withRunInIO f = withValid $ do
    env <- ask
    (liftIO $ catch (Right <$> f (runEquivM' env)) (\(e :: EquivalenceError arch) -> return $ Left e)) >>= \case
      Left err -> throwError err
      Right result -> return result

runEquivM' ::
  EquivEnv sym arch ->
  EquivM sym arch a ->
  IO a
runEquivM' env (EquivM f) = (runExceptT $ runReaderT f env) >>= \case
  Left err -> withValidEnv env $ throwIO err
  Right result -> return $ result

runEquivM ::
  EquivEnv sym arch ->
  EquivM sym arch a ->
  ExceptT (EquivalenceError arch) IO a
runEquivM env (EquivM f) = runReaderT f env

errorHere ::
  HasCallStack =>
  String ->
  EquivM sym arch a
errorHere msg = do
  let (_, src): _ = getCallStack callStack
  let msg' = "Error Message: " ++ msg ++ " at: " ++ prettySrcLoc src
  throwError $ EquivalenceError msg'

instance MonadFail (EquivM sym arch) where
  fail msg = errorHere $ "Fail: " ++ msg


_validTest :: (ValidArch RP.PPC64 => f) -> f
_validTest f = f

verifyPairs ::
  forall arch.
  ValidArch arch =>
  MBL.LoadedBinary arch (E.Elf 64) ->
  MBL.LoadedBinary arch (E.Elf 64) ->
  Map (R.ConcreteAddress arch) (R.ConcreteAddress arch) ->
  [R.RewritePair arch] ->
  ExceptT (EquivalenceError arch) IO ()
verifyPairs bin bin' ipMap pairs = do
  S.Some gen <- liftIO . stToIO $ N.newSTNonceGenerator
  vals <- case MS.archVals @arch Proxy of
    Nothing -> throwError UnsupportedArchitecture
    Just vs -> pure vs
  ha <- liftIO CFH.newHandleAllocator
  pfm  <- runDiscovery bin
  pfm' <- runDiscovery bin'

  S.Some gen' <- liftIO N.newIONonceGenerator
  let pfeats = W4PF.useBitvectors
  CBO.withYicesOnlineBackend W4B.FloatRealRepr gen' CBO.NoUnsatFeatures pfeats $ \sym -> do
    eval <- lift (MS.withArchEvalTrace vals sym pure)
    model <- lift (MT.mkMemTraceVar @arch ha)
    proc <- liftIO $ CBO.withSolverProcess sym return
    let
      exts = MS.macawTraceExtensions eval model (trivialGlobalMap @_ @arch)
      env = EquivEnv
        { originalCtx = BinaryContext
            { binary = bin
            , extensions = exts
            , globalMap = CGS.insertGlobal model mempty CGS.emptyGlobals
            , parsedFunctionMap = pfm
            }
        , rewrittenCtx = BinaryContext
            { binary = bin'
            , extensions = exts
            , globalMap = CGS.insertGlobal model mempty CGS.emptyGlobals
            , parsedFunctionMap = pfm'
            }
        , envSymProc = ValidOnlineBackend sym proc
        }
    
    runEquivM env $ do
      ipEq <- mkIPEquivalence ipMap

      let ctxt = EquivalenceContext
            { nonces = gen
            , handles = ha
            , archVals = vals
            , exprBuilder = ValidOnlineBackend sym proc
            , memTraceVar = model
            , ipEquivalence = ipEq
            }

      stats <- foldMapA (checkAndDisplayRenEquivalence ctxt) pairs
      liftIO . putStr $ ppEquivalenceStatistics stats

-- In newer GHCs, this is \f -> getAp . foldMap (Ap . f)
foldMapA :: (Foldable f, Applicative g, Monoid m) => (a -> g m) -> f a -> g m
foldMapA f = foldr (liftA2 (<>) . f) (pure mempty)

data EquivalenceStatistics = EquivalenceStatistics
  { numPairsChecked :: Int
  , numEquivalentPairs :: Int
  , numPairsErrored :: Int
  } deriving (Eq, Ord, Read, Show)

instance Semigroup EquivalenceStatistics where
  EquivalenceStatistics checked total errored <> EquivalenceStatistics checked' total' errored' = EquivalenceStatistics
    (checked + checked')
    (total + total')
    (errored + errored')

instance Monoid EquivalenceStatistics where
  mempty = EquivalenceStatistics 0 0 0

ppEquivalenceStatistics :: EquivalenceStatistics -> String
ppEquivalenceStatistics (EquivalenceStatistics checked equiv err) = unlines
  [ "Summary of checking " ++ show checked ++ " pairs:"
  , "\t" ++ show equiv ++ " equivalent"
  , "\t" ++ show (checked-equiv-err) ++ " inequivalent"
  , "\t" ++ show err ++ " skipped due to errors"
  ]

checkAndDisplayRenEquivalence ::
  EquivalenceContext sym ids arch ->
  R.RewritePair arch ->
  EquivM sym arch EquivalenceStatistics
checkAndDisplayRenEquivalence ctxt pair = withValid $ do
  liftIO . putStr $ ""
    ++ "Checking equivalence of "
    ++ formatBlock (R.rpOrig pair)
    ++ " and "
    ++ maybe "itself" formatBlock (R.rpNew pair)
    ++ ": "
  liftIO $ hFlush stdout
  eq <- manifestError $ checkRenEquivalence ctxt pair
  liftIO . putStr . ppEquivalenceResult $ eq
  pure $ case eq of
    Left _ -> EquivalenceStatistics 1 0 1
    Right Equivalent -> EquivalenceStatistics 1 1 0
    _ -> EquivalenceStatistics 1 0 0
  where
  formatBlock b = ""
    -- 100k oughta be enough for anybody
    ++ pad 6 (show (blockSize b))
    ++ " bytes at "
    ++ show (R.absoluteAddress (concreteAddress b))

padWith :: Char -> Int -> String -> String
padWith c n s = replicate (n-length s) c ++ s

pad :: Int -> String -> String
pad = padWith ' '

data GroundLLVMPointer = GroundLLVMPointer
  { ptrWidth :: Natural
  , ptrRegion :: Natural
  , ptrOffset :: Integer
  } deriving (Eq, Ord, Read, Show)

type family ConcreteValue (tp :: CC.CrucibleType)
type instance ConcreteValue (CLM.LLVMPointerType w) = GroundLLVMPointer

data RegisterDiff tp = RegisterDiff
  { rIndex :: Int
  , rTypeRepr :: CC.TypeRepr tp
  , rPre :: ConcreteValue tp
  , rPostOriginal :: ConcreteValue tp
  , rPostRewritten :: ConcreteValue tp
  , rPostEquivalent :: Bool
  }

data MemOpSpine
  = MemOpSpine MT.MemOpDirection Natural MM.Endianness
  | MergeSpines MemTraceSpine MemTraceSpine

type MemTraceSpine = Seq MemOpSpine

spineOf :: MT.MemTraceImpl sym ptrW -> MemTraceSpine
spineOf = fmap go where
  go (MT.MemOp _addr dir _cond size _val end) = MemOpSpine dir (W4.natValue size) end
  go (MT.MergeOps _cond traceT traceF) = MergeSpines (spineOf traceT) (spineOf traceF)

data GroundMemOp = GroundMemOp
  { gAddress :: GroundLLVMPointer
  , gCondition :: Bool
  , gValue :: GroundLLVMPointer
  } deriving (Eq, Ord, Read, Show)

data MemOpDiff = MemOpDiff
  { mDirection :: MT.MemOpDirection
  , mOpOriginal :: GroundMemOp
  , mOpRewritten :: GroundMemOp
  } deriving (Eq, Ord, Read, Show)

type MemTraceDiff = Seq MemOpDiff

data EquivalenceResult arch
  = Equivalent
  | InequivalentResults MemTraceDiff (Ctx.Assignment RegisterDiff (MS.MacawCrucibleRegTypes arch))
  | InequivalentOperations MemTraceSpine MemTraceSpine

combineEquivalence :: Monad m =>
  m (EquivalenceResult arch) ->
  m (EquivalenceResult arch) ->
  m (EquivalenceResult arch)
combineEquivalence act1 act2 = do
  res1 <- act1
  case res1 of
    Equivalent -> act2
    _ -> pure res1

checkRenEquivalence ::
  forall sym arch ids.
  EquivalenceContext sym ids arch ->
  R.RewritePair arch ->
  EquivM sym arch (EquivalenceResult arch)
checkRenEquivalence
  eqCtx@EquivalenceContext
    { archVals = MS.ArchVals { MS.archFunctions = fns }
    , handles = ha
    , exprBuilder = ValidOnlineBackend sym _
    , memTraceVar = mem
    }
  (R.RewritePair rBlock (Just rBlock')) = withValid $ do
  unconstrainedRegs_ <- Ctx.traverseWithIndex
    unconstrainedRegister
    (CC.knownRepr @_ @(Ctx.Assignment CC.TypeRepr) @(MS.MacawCrucibleRegTypes arch))
  let unconstrainedRegs = CS.assignReg CC.knownRepr unconstrainedRegs_ CS.emptyRegMap
  oCtx <- asks originalCtx
  rCtx <- asks rewrittenCtx
  (CS.RegEntry (CC.StructRepr regsRepr) regs, memTrace)
    <- simulate oCtx rBlock  Original  unconstrainedRegs
  (CS.RegEntry _ regs', memTrace')
    <- simulate rCtx rBlock' Rewritten unconstrainedRegs
  preds <- Ctx.traverseWithIndex (\i _ -> equivPred eqCtx regsRepr regs regs' i) regsRepr
  registersEquivalent <- TFC.foldrFC (<&&>) (pure (W4.truePred sym)) preds
  let
    matchTraces ::
      W4.Pred sym ->
      MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
      MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
      EquivM sym arch (EquivalenceResult arch)
    matchTraces prevChecks
      (MT.MergeOps p  traceT  traceF  :< ops )
      (MT.MergeOps p' traceT' traceF' :< ops')
      = combineEquivalence
        (errorFrame sym $ do
          prevChecks' <- liftIO $ do
            -- TODO: Does this do the right thing if we assume false? (The
            -- right thing for our case is for all checkSats in this frame to
            -- succeed.)
            CB.addAssumption sym (CB.LabeledPred p undefined)
            W4.andPred sym prevChecks p'
          matchTraces prevChecks' (traceT <> ops) (traceT' <> ops')
        )
        (errorFrame sym $ do
          prevChecks' <- liftIO $ do
            notp <- W4.notPred sym p
            notp' <- W4.notPred sym p'
            CB.addAssumption sym (CB.LabeledPred notp undefined)
            W4.andPred sym prevChecks notp'
          matchTraces prevChecks' (traceF <> ops) (traceF' <> ops')
        )
    matchTraces prevChecks
      (MT.MemOp addr  dir  cond_  w  val  end  :< ops )
      (MT.MemOp addr' dir' cond'_ w' val' end' :< ops')
      | Just Refl <- testEquality w w'
      , (dir, end) == (dir', end')
      = do
        prevChecks'' <- do
          cond <- memOpCondition cond_
          cond' <- memOpCondition cond'_
          withSymIO $ \_sym -> do
            condPred <- W4.eqPred sym cond cond'
            addrPred <- llvmPtrEq sym addr addr'
            prevChecks' <- W4.andPred sym prevChecks =<< W4.andPred sym condPred addrPred
            eqVal <- llvmPtrEq sym val val'
            here <- W4.getCurrentProgramLoc sym -- uh...
            case dir of
              MT.Read -> prevChecks' <$ CB.addAssumption sym (CB.LabeledPred eqVal (CB.AssumptionReason here "Equivalent reads give equal results"))
              MT.Write -> W4.andPred sym prevChecks' eqVal
        matchTraces prevChecks'' ops ops'

    matchTraces prevChecks Empty Empty = do
      notPrevChecks <- liftIO $ W4.notPred sym prevChecks
      -- TODO: addAssertion sym prevChecks ?
      checkSatisfiableWithModel satResultDescription notPrevChecks $ \case
        W4R.Unsat _ -> pure Equivalent
        W4R.Unknown -> throwError InconclusiveSAT
        W4R.Sat (W4G.GroundEvalFn fn) -> pure InequivalentResults
          <*> groundTraceDiff fn memTrace memTrace'
          <*> Ctx.traverseWithIndex
            (\i repr -> do
              pre <- concreteValue fn repr $ unconstrainedRegs_ Ctx.! i
              post <- concreteValue fn repr $ regs Ctx.! i
              post' <- concreteValue fn repr $ regs' Ctx.! i
              equiv <- liftIO . fn . getConst $ preds Ctx.! i
              pure RegisterDiff
                { rIndex = Ctx.indexVal i
                , rTypeRepr = repr
                , rPre = pre
                , rPostOriginal = post
                , rPostRewritten = post'
                , rPostEquivalent = equiv
                }
            )
            regsRepr
    matchTraces _ _ _ = pure (InequivalentOperations (spineOf memTrace) (spineOf memTrace'))
  matchTraces registersEquivalent memTrace memTrace'
  where
  evalCFG ::
    CS.RegMap sym tp ->
    BinaryContext sym arch ->
    CC.CFG (MS.MacawExt arch) blocks tp (MS.ArchRegStruct arch) ->
    EquivM sym arch (CS.ExecResult (MS.MacawSimulatorState sym) sym (MS.MacawExt arch) (CS.RegEntry sym (MS.ArchRegStruct arch)))
  evalCFG regs binCtx cfg = do
    archRepr <- getArchRepr
    let
      globals = globalMap binCtx
      exts = extensions binCtx
    withValidIO $ id
      . CS.executeCrucible []
      . CS.InitialState ( simContext exts) globals CS.defaultAbortHandler archRepr
      . CS.runOverrideSim archRepr
      $ CS.regValue <$> CS.callCFG cfg regs
  simContext exts = CS.initSimContext
    sym
    MT.memTraceIntrinsicTypes
    ha
    stderr
    CFH.emptyHandleMap
    exts
    MS.MacawSimulatorState
  satResultDescription = ""
        ++ "equivalence of the blocks at " ++ show (concreteAddress rBlock) ++ " in the original binary "
        ++ "and at " ++ show (concreteAddress rBlock') ++ " in the rewritten binary"

  simulate binCtx rb wb regs = errorFrame sym $ do
    -- rBlock/rb for renovate-style block, mBlocks/mbs for macaw-style blocks
    CC.SomeCFG cfg <- do
      CC.Some (Compose pbs_) <- lookupBlocks wb (parsedFunctionMap binCtx) rb
      let pb:pbs = sortOn MD.pblockAddr pbs_
          -- There's a slight hack here.
          --
          -- The core problem we're dealing with here is that renovate blocks
          -- can have multiple basic blocks; and almost always do in the
          -- rewritten binary. We want to stitch them together in the right
          -- way, and part of that means deciding whether basic block
          -- terminators are things we should "follow" to their target to
          -- continue symbolically executing or not. Normally any block
          -- terminator that goes to another basic block in the same renovate
          -- block is one we want to keep symbolically executing through.
          --
          -- BUT if there is an actual self-contained loop within a single
          -- renovate block, we want to avoid trying to symbolically execute
          -- that forever, so we'd like to pick some of the edges in the
          -- "block X can jump to block Y" graph that break all the cycles,
          -- and mark all of those as terminal for the purposes of CFG
          -- creation.
          --
          -- Instead of doing a careful analysis of that graph, we adopt the
          -- following heuristic: kill any edges that point to the entry
          -- point of the renovate block, and symbolically execute through
          -- all the others. This catches at the very least any
          -- single-basic-block loops in the original binary and in most
          -- cases even their transformed version in the rewritten binary. If
          -- we ever kill such an edge, we have certainly broken a cycle; but
          -- cycles could appear in other ways that we don't catch.
          --
          -- This heuristic is reflected in the code like this: when deciding
          -- if a jump should be killed, we compare jump targets to a
          -- collection of "internal" addresses, and kill it if the target
          -- isn't in that collection. Then we omit the entry point's address
          -- from that collection, so that jumps to it are considered terminal.

          -- Multiple ParsedBlocks may have the same address, so the delete
          -- is really needed.
          internalAddrs = S.delete (MD.pblockAddr pb) $ S.fromList [MD.pblockAddr b | b <- pbs]
          (terminal_, nonTerminal) = partition isTerminalBlock pbs
          terminal = [pb | isTerminalBlock pb] ++ terminal_
          killEdges = concatMap (externalTransitions internalAddrs) (pb:pbs)
      liftIO $ MS.mkBlockSliceCFG fns ha (W4L.OtherPos . fromString . show) pb nonTerminal terminal killEdges
    -- TODO: constrain the IP and LNK register
    cres <- evalCFG regs binCtx cfg
    getGPValueAndTrace mem cres

  Const p1 <&&> mp2 = mp2 >>= liftIO . W4.andPred sym p1

-- Even if we don't rewrite anything, we should still check that the return
-- addresses are equivalent according to the equivalence relation we've built
-- up for IPs. This could go wrong, for example, if we should have rewritten a
-- jump but didn't.
--
-- The way this is done below is cheap in programmer time but expensive in
-- computer time: just check that the whole block is equivalent to itself by
-- symbolically simulating it twice. We could imagine doing a more efficient
-- check in the future that just looks at the terminal statement of the
-- block(s) and checks that they go to equivalent locations without fully
-- symbolically simulating the thing.
checkRenEquivalence eqCtx (R.RewritePair rBlock Nothing) =
  R.withConcreteInstructions rBlock $ \repr insns ->
    let rBlock' = R.concretizedBlock (R.concreteBlockAddress rBlock) insns repr
    in checkRenEquivalence eqCtx (R.RewritePair rBlock (Just rBlock'))


getArchRepr :: forall sym arch. EquivM sym arch (CC.TypeRepr (MS.ArchRegStruct arch))
getArchRepr = withValid $ return $ CC.knownRepr @_ @_ @(MS.ArchRegStruct arch)

memOpCondition :: MT.MemOpCondition sym -> EquivM sym arch (W4.Pred sym)
memOpCondition = \case
  MT.Unconditional -> withSymIO $ \sym -> return $ W4.truePred sym
  MT.Conditional p -> return p

runInIO1 :: IO.MonadUnliftIO m => (a -> m b) -> ((a -> IO b) -> IO b) -> m b
runInIO1 f g = do
  IO.UnliftIO outer_io_ctx <- IO.askUnliftIO
  liftIO $ g (\a -> outer_io_ctx (f a))

checkSatisfiableWithModel ::
  ValidSolver sym scope solver fs =>
  String ->
  W4B.BoolExpr scope ->
  (W4R.SatResult (W4G.GroundEvalFn scope) () -> EquivM sym arch a) ->
  EquivM sym arch a
checkSatisfiableWithModel desc p k = withProc $ \proc ->
  runInIO1 k $ W4O.checkSatisfiableWithModel proc desc p


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

isTerminalBlock :: MD.ParsedBlock arch ids -> Bool
isTerminalBlock pb = case MD.pblockTermStmt pb of
  MD.ParsedCall{} -> True
  MD.PLTStub{} -> True
  MD.ParsedJump{} -> False
  MD.ParsedBranch{} -> False
  MD.ParsedLookupTable{} -> False
  MD.ParsedReturn{} -> False
  MD.ParsedArchTermStmt{} -> True -- TODO: think harder about this
  MD.ParsedTranslateError{} -> True
  MD.ClassifyFailure{} -> True

externalTransitions ::
  Set (MM.ArchSegmentOff arch) ->
  MD.ParsedBlock arch ids ->
  [(MM.ArchSegmentOff arch, MM.ArchSegmentOff arch)]
externalTransitions internalAddrs pb =
  [ (MD.pblockAddr pb, tgt)
  | tgt <- case MD.pblockTermStmt pb of
      MD.ParsedCall{} -> []
      MD.PLTStub{} -> []
      MD.ParsedJump _ tgt -> [tgt]
      MD.ParsedBranch _ _ tgt tgt' -> [tgt, tgt']
      MD.ParsedLookupTable _ _ tgts -> toList tgts
      MD.ParsedReturn{} -> []
      MD.ParsedArchTermStmt{} -> [] -- TODO: think harder about this
      MD.ParsedTranslateError{} -> []
      MD.ClassifyFailure{} -> []
  , tgt `S.notMember` internalAddrs
  ]

equivPred ::
  Ctx.KnownContext ctx =>
  EquivalenceContext sym ids arch ->
  Ctx.Assignment CC.TypeRepr ctx ->
  Ctx.Assignment (CS.RegValue' sym) ctx ->
  Ctx.Assignment (CS.RegValue' sym) ctx ->
  Ctx.Index ctx tp ->
  EquivM sym arch (Const (W4.Pred sym) tp)
equivPred
  EquivalenceContext { exprBuilder = ValidOnlineBackend sym _, ipEquivalence = ipEq }
  regsRepr regs regs' i
  = withValid $ Const <$> case regsRepr Ctx.! i of
    CLM.LLVMPointerRepr widthRepr -> liftIO $ case (regs Ctx.! i, regs' Ctx.! i) of
      (CS.RV bv, CS.RV bv')
        -- TODO: abstract away the 0 and 64
        | Just (CC.Some idx) <- Ctx.intIndex 0 Ctx.knownSize
        , Just Refl <- testEquality i idx
        , Just Refl <- testEquality widthRepr (W4.knownNat @64) -> ipEq bv bv'
        -- TODO: What to do with the link register (index 1 in the current
        -- register struct for PPC64)? Is ipEq good enough? Things to worry
        -- about with that choice:
        -- 1. We should probably initialize the link register somehow for both
        -- blocks so that the register starts out equivalent. Would be sort of
        -- a shame to declare blocks inequivalent because they both started
        -- with 0 in their LR and didn't change that.
        -- 2. ipEq declares the starts of blocks equivalent. blr tends to come
        -- at the end of blocks, not the start.
        | otherwise -> llvmPtrEq sym bv bv'
    repr -> throwError (UnsupportedRegisterType (S.Some repr))

concreteValue ::
  (forall tp'. W4B.Expr scope tp' -> IO (W4G.GroundValue tp')) ->
  CC.TypeRepr tp ->
  CS.RegValue' (CBO.OnlineBackend scope solver fs) tp ->
  EquivM sym arch (ConcreteValue tp)
concreteValue fn (CLM.LLVMPointerRepr widthRepr) (CS.RV (CLM.LLVMPointer symRegion symOffset)) = liftIO $ do
  region <- fn symRegion
  offset <- fn symOffset
  pure GroundLLVMPointer
    { ptrWidth = W4.natValue widthRepr
    , ptrRegion = region
    , ptrOffset = BVS.asSigned widthRepr offset
    }
concreteValue _ repr _ = throwError (UnsupportedRegisterType (S.Some repr))

-- We assume the two traces have equivalent spines already.
groundTraceDiff ::
  (forall tp. W4B.SymExpr sym tp -> IO (W4G.GroundValue tp)) ->
  MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
  MT.MemTraceImpl sym (MM.ArchAddrWidth arch) ->
  EquivM sym arch MemTraceDiff
groundTraceDiff fn (MT.MemOp addr dir cond_ w val _ :< ops) (MT.MemOp addr' _ cond'_ w' val' _ :< ops') = do
  cond <- memOpCondition cond_
  cond' <- memOpCondition cond'_  
  op  <- groundMemOp fn addr  cond  w  val
  op' <- groundMemOp fn addr' cond' w' val'
  diff <- groundTraceDiff fn ops ops'
  pure (MemOpDiff
    { mDirection = dir
    , mOpOriginal = op
    , mOpRewritten = op'
    } :< diff)
groundTraceDiff fn (MT.MergeOps cond traceT traceF :< ops) (MT.MergeOps _cond' traceT' traceF' :< ops') = do
  b <- liftIO (fn cond)
  let (trace, trace') = if b then (traceT, traceT') else (traceF, traceF')
  groundTraceDiff fn (trace <> ops) (trace' <> ops')
groundTraceDiff _fn Empty Empty = pure Empty
groundTraceDiff _ _ _ = error "The impossible happened: groundTraceDiff was called on memory traces that were not equivalent"

groundMemOp ::
  (forall tp. W4B.SymExpr sym tp -> IO (W4G.GroundValue tp)) ->
  CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
  W4.Pred sym ->
  W4.NatRepr w ->
  CLM.LLVMPtr sym w ->
  EquivM sym arch GroundMemOp
groundMemOp fn addr cond w val = withValid $ liftA3 GroundMemOp
  (groundLLVMPointer fn W4.knownRepr addr)
  (liftIO (fn cond))
  (groundLLVMPointer fn w val)

groundLLVMPointer ::
  (forall tp. W4B.SymExpr sym tp -> IO (W4G.GroundValue tp)) ->
  W4.NatRepr w ->
  CLM.LLVMPtr sym w ->
  EquivM sym arch GroundLLVMPointer
groundLLVMPointer fn w (CLM.LLVMPointer reg off) = liftIO $ do
  greg <- fn reg
  goff <- fn off
  pure GroundLLVMPointer
    { ptrWidth = W4.natValue w
    , ptrRegion = greg
    , ptrOffset = BVS.asUnsigned goff
    }

ppEquivalenceResult :: MM.MemWidth (MM.ArchAddrWidth arch) => Either (EquivalenceError arch) (EquivalenceResult arch) -> String
ppEquivalenceResult (Right Equivalent) = "✓\n"
ppEquivalenceResult (Right (InequivalentResults traceDiff regDiffs)) = "x\n" ++ ppPreRegs regDiffs ++ ppMemTraceDiff traceDiff ++ ppDiffs regDiffs
ppEquivalenceResult (Right (InequivalentOperations trace trace')) = concat
  [ "x\n\tMismatched memory operations:\n\t\t"
  , ppMemTraceSpine trace
  , " (original) vs.\n\t\t"
  , ppMemTraceSpine trace'
  , " (rewritten)\n"
  ]
ppEquivalenceResult (Left err) = "-\n\t" ++ show err ++ "\n" -- TODO: pretty-print the error

ppMemTraceDiff :: MemTraceDiff -> String
ppMemTraceDiff diffs = "\tTrace of memory operations:\n" ++ concatMap ppMemOpDiff (toList diffs)

ppMemOpDiff :: MemOpDiff -> String
ppMemOpDiff diff
  =  "\t\t" ++ ppDirectionVerb (mDirection diff) ++ " "
  ++ ppGroundMemOp (mDirection diff) (mOpOriginal diff)
  ++ (if mOpOriginal diff == mOpRewritten diff
      then ""
      else " (original) vs. " ++ ppGroundMemOp (mDirection diff) (mOpRewritten diff) ++ " (rewritten)"
     )
  ++ "\n"

ppGroundMemOp :: MT.MemOpDirection -> GroundMemOp -> String
ppGroundMemOp dir op
  =  ppLLVMPointer (gValue op)
  ++ " " ++ ppDirectionPreposition dir ++ " "
  ++ ppLLVMPointer (gAddress op)
  ++ if gCondition op
     then ""
     else " (skipped)"

ppDirectionVerb :: MT.MemOpDirection -> String
ppDirectionVerb MT.Read = "read"
ppDirectionVerb MT.Write = "wrote"

ppDirectionPreposition :: MT.MemOpDirection -> String
ppDirectionPreposition MT.Read = "from"
ppDirectionPreposition MT.Write = "to"

ppMemTraceSpine :: MemTraceSpine -> String
ppMemTraceSpine = unwords . map ppMemOpSpine . toList

ppMemOpSpine :: MemOpSpine -> String
ppMemOpSpine (MemOpSpine dir size end) = concat
  [ take 1 (ppDirectionVerb dir)
  , ppEndianness end
  , show size
  ]
ppMemOpSpine (MergeSpines spineT spineF) = concat
  [ "("
  , ppMemTraceSpine spineT
  , "/"
  , ppMemTraceSpine spineF
  , ")"
  ]

ppEndianness :: MM.Endianness -> String
ppEndianness MM.BigEndian = "→"
ppEndianness MM.LittleEndian = "←"

ppPreRegs :: Ctx.Assignment RegisterDiff ctx -> String
ppPreRegs diffs = "\tInitial registers of a counterexample:\n" ++ case TFC.foldMapFC ppPreReg diffs of
  (Sum 0, s) -> s
  (Sum n, s) -> s ++ "\t\t(and " ++ show n ++ " other all-zero slots)\n"

ppPreReg :: RegisterDiff tp -> (Sum Int, String)
ppPreReg diff = case rTypeRepr diff of
  CLM.LLVMPointerRepr _ -> case rPre diff of
    GroundLLVMPointer _ 0 0 -> (1, "")
    _ -> (0, ppSlot diff ++ ppLLVMPointer (rPre diff) ++ "\n")
  _ -> (0, ppSlot diff ++ "unsupported register type in precondition pretty-printer\n")

ppDiffs :: Ctx.Assignment RegisterDiff ctx -> String
ppDiffs diffs = "\tMismatched resulting registers:\n" ++ TFC.foldMapFC ppDiff diffs

ppDiff :: RegisterDiff tp -> String
ppDiff diff | rPostEquivalent diff = ""
ppDiff diff = ppSlot diff ++ case rTypeRepr diff of
  CLM.LLVMPointerRepr _ -> ""
    ++ ppLLVMPointer (rPostOriginal diff)
    ++ " (original) vs. "
    ++ ppLLVMPointer (rPostRewritten diff)
    ++ " (rewritten)\n"
  _ -> "unsupported register type in postcondition comparison pretty-printer\n"

ppSlot :: RegisterDiff tp -> String
ppSlot diff = "\t\tslot " ++ (pad 4 . show . rIndex) diff ++ ": "

ppLLVMPointer :: GroundLLVMPointer -> String
ppLLVMPointer (GroundLLVMPointer bitWidth reg off) = ""
  ++ pad 3 (show reg)
  ++ "+0x"
  ++ padWith '0' (fromIntegral ((bitWidth+3)`div`4)) (showHex off "")

trivialGlobalMap :: MS.GlobalMap sym (MT.MemTrace arch) w
trivialGlobalMap _ _ reg off = pure (CLM.LLVMPointer reg off)

-- TODO: What should happen if the Pred sym in a PartialRes in pres or pres' is false?
getGPValueAndTrace ::
  CS.GlobalVar (MT.MemTrace arch) ->
  CS.ExecResult p sym ext (CS.RegEntry sym (MS.ArchRegStruct arch)) ->
  EquivM sym arch
    ( CS.RegEntry sym (MS.ArchRegStruct arch)
    , MT.MemTraceImpl sym (MM.ArchAddrWidth arch)
    )
getGPValueAndTrace mem (CS.FinishedResult _ pres) = withValid $ case pres ^. CS.partialValue of
  CS.GlobalPair val globs -> case CGS.lookupGlobal mem globs of
    Just mt -> pure (val, mt)
    Nothing -> throwError undefined
getGPValueAndTrace _mem (CS.AbortedResult _ ar) = throwError . SymbolicExecutionFailed . ppAbortedResult $ ar
getGPValueAndTrace _mem (CS.TimeoutResult _) = throwError (SymbolicExecutionFailed "timeout")

ppAbortedResult :: CS.AbortedResult sym ext -> String
ppAbortedResult (CS.AbortedExec reason _) = show reason
ppAbortedResult (CS.AbortedExit code) = show code
ppAbortedResult (CS.AbortedBranch loc _ t f) = "branch (@" ++ show loc ++ ") (t: " ++ ppAbortedResult t ++ ") (f: " ++ ppAbortedResult f ++ ")"

unconstrainedRegister ::
  Ctx.Index ctx tp ->
  CC.TypeRepr tp ->
  EquivM sym arch (CS.RegValue' sym tp)
unconstrainedRegister idx repr = do
  let name = "reg" ++ show (Ctx.indexVal idx)
  symbol <- either (throwError . InvalidRegisterName name) pure (W4S.userSymbol name)
  case repr of
    CLM.LLVMPointerRepr n -> withSymIO $ \sym -> do
      bv <- W4.freshConstant sym symbol (W4.BaseBVRepr n)
      -- TODO: This fixes the region to 0. Is that okay?
      ptr <- CLM.llvmPointer_bv sym bv
      pure (CS.RV ptr)
    _ -> throwError (UnsupportedRegisterType (S.Some repr))

-- | Keys: basic block extent; values: parsed blocks
newtype ParsedBlockMap arch ids = ParsedBlockMap
  { getParsedBlockMap :: IntervalMap (R.ConcreteAddress arch) [MD.ParsedBlock arch ids]
  }

-- | basic block extent -> function entry point -> basic block extent again -> parsed block
--
-- You should expect (and check) that exactly one key exists at the function entry point level.
type ParsedFunctionMap arch = IntervalMap (R.ConcreteAddress arch) (Map (MM.ArchSegmentOff arch) (CC.Some (ParsedBlockMap arch)))

markEntryPoint ::
  MM.ArchSegmentOff arch ->
  ParsedBlockMap arch ids ->
  ParsedFunctionMap arch
markEntryPoint segOff blocks = M.singleton segOff (CC.Some blocks) <$ getParsedBlockMap blocks

lookupBlocks ::
  ( MonadError (EquivalenceError arch) m
  , Concrete b
  , R.HasConcreteAddresses b
  , ValidArch arch
  ) =>
  WhichBinary ->
  ParsedFunctionMap arch ->
  b arch ->
  m (CC.Some (Compose [] (MD.ParsedBlock arch)))
lookupBlocks wb pfm b = case M.assocs . M.unions . IM.elems . IM.intersecting pfm $ i of
  [(_, CC.Some (ParsedBlockMap pbm))] -> do
    result <- fmap concat . traverse (pruneBlock wb start end) . concat . IM.elems . IM.intersecting pbm $ i
    sanityCheckBlockCoverage wb start end result
    pure (CC.Some (Compose result))
  segoffPBMPairs -> throwError $ NoUniqueFunctionOwner i (fst <$> segoffPBMPairs)
  where
  start = concreteAddress b
  end = start `R.addressAddOffset` fromIntegral (blockSize b)
  i = IM.IntervalCO start end

-- | Check that the given parsed blocks cover the entire range of bytes described by the given interval.
sanityCheckBlockCoverage ::
  (MonadError (EquivalenceError arch) m, MM.MemWidth (MM.ArchAddrWidth arch)) =>
  WhichBinary ->
  R.ConcreteAddress arch ->
  R.ConcreteAddress arch ->
  [MD.ParsedBlock arch ids] ->
  m ()
sanityCheckBlockCoverage wb start end pbs = do
  is <- sort <$> traverse parsedBlockToInterval pbs
  go start end is
  where
  parsedBlockToInterval pb = archSegmentOffToInterval (MD.pblockAddr pb) (MD.blockSize pb)
  go s e [] = when (s < e) (throwError (UndiscoveredBlockPart wb start s e))
  go s e (IM.IntervalCO s' e':is)
    | s < s' = throwError (UndiscoveredBlockPart wb start s s')
    | otherwise = go (max s e') e is
  go _ _ _ = error "Support for interval types other than IntervalCO not yet implemented in sanityCheckBlockCoverage.go"

-- Given an address range, modify the given ParsedBlock to only include
-- instructions from within that range. We have to decide what to do about
-- instructions that span the boundary.
--
-- Spanning the start address is fine in principle. We could just start the
-- block a bit later. This seems okay: if a renovate rewriter wants to spit out
-- some convoluted code that can be interpreted differently depending on
-- whether we start interpreting at the beginning of the block or somewhere in
-- the middle, that's fine for our purposes. However, for technical reasons, it
-- turns out to be quite difficult to strip off part of the beginning of a
-- ParsedBlock. So for now we throw away the ParsedBlock; in the future, it may
-- be possible to support this more gracefully.
--
-- Spanning the end address is not fine. We throw an error. This seems like it
-- generally shouldn't happen: a renovate rewriter shouldn't be emitting
-- partial instructions, and expecting that the block the layout engine chooses
-- to put afterwards has a sensible continuation of that instruction.
pruneBlock ::
  ( MonadError (EquivalenceError arch) m
  , MM.MemWidth (MM.ArchAddrWidth arch)
  ) =>
  WhichBinary ->
  R.ConcreteAddress arch ->
  R.ConcreteAddress arch ->
  MD.ParsedBlock arch ids ->
  m [MD.ParsedBlock arch ids]
pruneBlock wb start_ end_ pb = do
  pblockStart <- liftMaybe (MM.segoffAsAbsoluteAddr (MD.pblockAddr pb)) (NonConcreteParsedBlockAddress wb (MD.pblockAddr pb))
  let pblockEnd = pblockStart + fromIntegral (MD.blockSize pb)
  case (pblockStart < start, pblockEnd <= end) of
    -- TODO: Handle this more gracefully: instead of throwing the block away,
    -- strip some instructions off the beginning of the ParsedBlock. But take
    -- some care: the Stmts contain ArchStates that will be invalidated by this
    -- process; these will need to be fixed up.
    (True, _) -> pure []
    (_, True) -> pure [pb]
    _ -> do
      (stmts, updateTermStmt) <- findEnd (end - pblockStart) (MD.pblockStmts pb)
      case updateTermStmt of
        Nothing -> pure [pb { MD.pblockStmts = stmts }]
        Just (off, archState) -> do
          pblockEndSegOff <- blockOffAsSegOff off
          pure [pb
            { MD.pblockStmts = stmts
            , MD.blockSize = fromIntegral off
            , MD.pblockTermStmt = MD.ParsedJump (coerceArchState archState) pblockEndSegOff
            }]
  where
  findEnd size stmts = do
    archState <- findState stmts
    findEndHelper size archState stmts

  findEndHelper size _archState (stmt@(MM.ArchState _ archState):stmts) = addStmt stmt <$> findEndHelper size archState stmts
  findEndHelper size archState (stmt@(MM.InstructionStart off _):stmts) = case compare off size of
    LT -> addStmt stmt <$> findEndHelper size archState stmts
    EQ -> pure ([], Just (off, archState))
    GT -> throwError (BlockEndsMidInstruction wb) -- TODO: think about what information would be useful to report here
  findEndHelper size archState (stmt:stmts) = addStmt stmt <$> findEndHelper size archState stmts
  -- BEWARE! This base case is unusually subtle.
  --
  -- findEndHelper is currently only called under the condition:
  --
  --     pblockStart + fromIntegral (MD.blockSize pb) > end
  --
  -- that is, when we're definitely supposed to strip something off the end. SO
  -- if we haven't found where to start stripping, that means the final
  -- instruction of the discovered block crosses the end boundary of the
  -- renovate block.
  --
  -- In the future, when we start stripping from the beginning as well, it's
  -- possible that we may begin calling findEndHelper even when we are not
  -- certain we need to strip something, for uniformity/simplicity. If we do,
  -- then this base case will need to do that check, and possibly return ([],
  -- Nothing) if we do not cross the renovate block boundary.
  findEndHelper _size _archState [] = throwError (BlockEndsMidInstruction wb)

  findState [] = throwError PrunedBlockIsEmpty
  findState (MM.ArchState _ archState:_) = pure archState
  findState (_:stmts) = findState stmts

  addStmt stmt (stmts, updateTermStmt) = (stmt:stmts, updateTermStmt)

  blockOffAsSegOff off = liftMaybe
    (MM.incSegmentOff (MD.pblockAddr pb) (fromIntegral off))
    (BlockExceedsItsSegment wb (MD.pblockAddr pb) off)

  start = R.absoluteAddress start_
  end = R.absoluteAddress end_

  coerceArchState :: MapF r f -> MM.RegState r f
  coerceArchState = unsafeCoerce

liftMaybe :: MonadError e m => Maybe a -> e -> m a
liftMaybe Nothing e = throwError e
liftMaybe (Just a) _ = pure a

runDiscovery ::
  ValidArch arch =>
  MBL.LoadedBinary arch (E.Elf 64) ->
  ExceptT (EquivalenceError arch) IO (ParsedFunctionMap arch)
runDiscovery bin = do
  entries <- toList <$> MBL.entryPoints bin
  goDiscoveryState $
    MD.cfgFromAddrs (MP.ppc64_linux_info bin) (MBL.memoryImage bin) M.empty entries []
  where
  goDiscoveryState ds = id
    . fmap (IM.unionsWith M.union)
    . mapM goSomeDiscoveryFunInfo
    . M.assocs
    $ ds ^. MD.funInfo
  goSomeDiscoveryFunInfo (entrySegOff, CC.Some dfi) = markEntryPoint entrySegOff <$> goDiscoveryFunInfo dfi
  goDiscoveryFunInfo dfi = fmap (ParsedBlockMap . IM.fromListWith (++)) . sequence $
    [ (\addrs -> (addrs, [pb])) <$> archSegmentOffToInterval blockSegOff (MD.blockSize pb)
    | (blockSegOff, pb) <- M.assocs (dfi ^. MD.parsedBlocks)
    ]

archSegmentOffToInterval ::
  (MonadError (EquivalenceError arch) m, MM.MemWidth (MM.ArchAddrWidth arch)) =>
  MM.ArchSegmentOff arch ->
  Int ->
  m (IM.Interval (R.ConcreteAddress arch))
archSegmentOffToInterval segOff size = case MM.segoffAsAbsoluteAddr segOff of
  Just w -> pure (IM.IntervalCO start (start `R.addressAddOffset` fromIntegral size))
    where start = R.concreteFromAbsolute w
  Nothing -> throwError (StrangeBlockAddress segOff)

class Concrete b where
  concreteAddress :: b arch -> R.ConcreteAddress arch

instance Concrete R.ConcreteBlock where
  concreteAddress = R.concreteBlockAddress

instance Concrete R.ConcretizedBlock where
  concreteAddress = R.concretizedBlockAddress

blockSize :: forall arch b. ValidArch arch => (R.HasConcreteAddresses b) => b arch -> Int
blockSize = fromIntegral . R.blockSize isa
  where
    isa = RP.isa @arch

mkIPEquivalence ::
  Map (R.ConcreteAddress arch) (R.ConcreteAddress arch) ->
  EquivM sym arch (
    CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
    CLM.LLVMPtr sym (MM.ArchAddrWidth arch) ->
    IO (W4.Pred sym)
    )
mkIPEquivalence ipMap = withValid $ do
  ips' <- traverse (concreteToLLVM . fst) assocs
  ips <- traverse (concreteToLLVM . snd) assocs
  [regSS, offSS, regSS', offSS', ipEqSS] <- traverse userSymbol
    ["orig_reg", "orig_off", "rewrite_reg", "rewrite_off", "related_ips"]

  withSymIO $ \sym -> do
    regionVar  <- W4.freshBoundVar sym regSS  W4.knownRepr
    offsetVar  <- W4.freshBoundVar sym offSS  W4.knownRepr
    regionVar' <- W4.freshBoundVar sym regSS' W4.knownRepr
    offsetVar' <- W4.freshBoundVar sym offSS' W4.knownRepr

    let ipArg  = CLM.LLVMPointer (W4.varExpr sym regionVar ) (W4.varExpr sym offsetVar )
        ipArg' = CLM.LLVMPointer (W4.varExpr sym regionVar') (W4.varExpr sym offsetVar')
        iop <&&> iop' = do
          p  <- iop
          p' <- iop'
          W4.andPred sym p p'
    alternatives <- flipZipWithM ips ips' $ \ip ip' -> llvmPtrEq sym ipArg ip <&&> llvmPtrEq sym ipArg' ip'
    anyAlternative <- foldM (W4.orPred sym) (W4.falsePred sym) alternatives

    ipEqSymFn <- W4.definedFn sym
      ipEqSS
      (Ctx.empty `Ctx.extend` regionVar `Ctx.extend` offsetVar `Ctx.extend` regionVar' `Ctx.extend` offsetVar')
      anyAlternative
      W4.UnfoldConcrete

    pure $ \(CLM.LLVMPointer region offset) (CLM.LLVMPointer region' offset') -> W4.applySymFn sym ipEqSymFn
      (Ctx.empty `Ctx.extend` region `Ctx.extend` offset `Ctx.extend` region' `Ctx.extend` offset')
  where
  assocs = M.assocs ipMap


flipZipWithM :: Monad m => [a] -> [b] -> (a -> b -> m c) -> m [c]
flipZipWithM as bs f = zipWithM f as bs

userSymbol :: String -> EquivM sym arch W4.SolverSymbol
userSymbol s = case W4.userSymbol s of
  Left err -> throwError (BadSolverSymbol s err)
  Right ss -> pure ss

concreteToLLVM ::
  ( 
   w ~ MM.ArchAddrWidth arch, MM.MemWidth w, KnownNat w, 1 <= w
  ) =>
  R.ConcreteAddress arch ->
  EquivM sym arch (CLM.LLVMPtr sym w)
concreteToLLVM c = withSymIO $ \sym -> do
  region <- W4.natLit sym 0
  offset <- W4.bvLit sym W4.knownRepr (BVS.mkBV W4.knownRepr (toInteger (R.absoluteAddress c)))
  pure (CLM.LLVMPointer region offset)

llvmPtrEq ::
  CB.IsSymInterface sym =>
  sym ->
  CLM.LLVMPtr sym w ->
  CLM.LLVMPtr sym w ->
  IO (W4.Pred sym)
llvmPtrEq sym (CLM.LLVMPointer region offset) (CLM.LLVMPointer region' offset') = do
  regionsEq <- W4.isEq sym region region'
  offsetsEq <- W4.isEq sym offset offset'
  W4.andPred sym regionsEq offsetsEq
