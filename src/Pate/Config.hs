{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Pate.Config (
  PatchData(..),
  BlockAlignment(..),
  Address(..),
  Allocation(..),
  EquatedFunction(..),
  MemRegion(..),
  parsePatchConfig,
  VerificationConfig(..),
  VerificationMethod(..),
  defaultVerificationCfg
  ) where

import qualified Control.Monad.Except as CME
import qualified Control.Monad.State as CMS
import qualified Data.ByteString as BS
import qualified Data.HashMap.Strict as DHS
import qualified Data.Text.Encoding as DTE
import qualified Data.Text.Encoding.Error as DTEE
import           Numeric.Natural ( Natural )
import           Text.Printf ( PrintfArg, printf )
import qualified Toml
import           Toml ( (.=) )
import           Numeric (readHex)

import qualified Pate.Solver as PS
import qualified Pate.Timeout as PT

-- | A newtype wrapper for a number representing an address
--
-- This is primarily to provide nice rendering as a hex value when printed, but
-- also as useful documentation. These are abstract user-provided addresses that
-- still need to be mapped to macaw/crucible addresses before they are used.
newtype Address = Address { addressAsWord :: Natural }
  deriving (Eq, Ord, Num, PrintfArg)

instance Show Address where
  show (Address w) = printf "0x%x" w

instance Read Address where
  readsPrec _ s = do
    (n, s') <- readHex s
    return $ (Address n, s')

-- | A region of memory, specified as a start address and a length (in bytes).
data MemRegion =
  MemRegion{ memRegionStart :: Address, memRegionLength :: Natural }

instance Show MemRegion where
  show (MemRegion (Address start) len) = printf "start: 0x%x length: %d" start len

memRegionCodec :: Toml.TomlCodec MemRegion
memRegionCodec = MemRegion
  <$> Toml.diwrap (Toml.natural "start-address") .= memRegionStart
  <*> Toml.diwrap (Toml.natural "length") .= memRegionLength

-- | A pair of addresses that helps the verifier align two basic blocks that
-- might otherwise seem unrelated
data BlockAlignment =
  BlockAlignment { originalBlockStart :: Address, patchedBlockStart :: Address }
  deriving (Show)

blockAlignmentCodec :: Toml.TomlCodec BlockAlignment
blockAlignmentCodec = BlockAlignment
  <$> Toml.diwrap (Toml.natural "original-block-address") .= originalBlockStart
  <*> Toml.diwrap (Toml.natural "patched-block-address") .= patchedBlockStart

-- | A descriptor for an allocation for use with the "ignore pointers"
-- functionality in the inline callee feature
--
-- Note that it is likely that we will want to extend this type with additional
-- allocation types (e.g., ones where the memory address is known directly,
-- rather than indirectly through the address of a pointer)
data Allocation =
  GlobalPointerAllocation { pointerAddress :: Address, blockSize :: Natural }
  deriving (Show)

allocationCodec :: Toml.TomlCodec Allocation
allocationCodec = GlobalPointerAllocation
  <$> Toml.diwrap (Toml.natural "pointer-address") .= pointerAddress
  <*> Toml.natural "block-size" .= blockSize

data EquatedFunction =
  EquatedFunction { originalEquatedFunction :: Address, patchedEquatedFunction :: Address }
  deriving (Show)

equatedFunctionCodec :: Toml.TomlCodec EquatedFunction
equatedFunctionCodec = EquatedFunction
  <$> Toml.diwrap (Toml.natural "original-function-address") .= originalEquatedFunction
  <*> Toml.diwrap (Toml.natural "patched-function-address") .= patchedEquatedFunction

data PatchData =
  PatchData { patchPairs :: [BlockAlignment]
            -- ^ Hints to align pairs of basic blocks in cases where they do not
            -- align in a way discoverable by the verifier.
            --
            -- This is most commonly used to specify custom entry points
            , ignoreOriginalAllocations :: [Allocation]
            -- ^ For the original and patched program, each may come with a list of
            --   "ignorable" pointers.  Each pair in the list consists of a location
            --   and a length.  The locations refer to positions in the global memory
            --   of the programs where pointers may be stored during the program run.
            --   The regions of memory pointed to (with the given length) are inteded
            --   to be ignored by the verifier, so that differences between the two runs
            --   do not result in equivalence failures. Note that this is an _indirect_
            --   notion of ignorability; the locations specified here are themselves
            --   are not ignored, but rather the memory to which they point.
            , ignorePatchedAllocations :: [Allocation]

            , equatedFunctions :: [EquatedFunction]
            -- ^ Pairs of functions (named by their address) that should be
            -- considered to be equivalent, even if they actually have different
            -- effects. This is intended to work with the 'ignorePointers'
            -- feature to enable users to specify that memory changes to certain
            -- memory locations should be ignored, while verifying that the side
            -- effects of the 'equatedFunctions' are benign.
            --
            -- The functions in this list are paired up by call site, and must
            -- be called at aligned call sites in the original and patched
            -- binaries, respectively.
            --
            -- See the documentation on the function replacement verification
            -- feature.
            , ignoreOriginalFunctions :: [Address]
            -- ^ A list of addresses of function calls to ignore from the
            -- original binary. If the verifier sees a call to a function in
            -- this list in the original binary, it will treat the call as a
            -- no-op.
            , ignorePatchedFunctions :: [Address]
            -- ^ The same as 'ignoreOriginalFunctions', but for the patched binary
            --
            -- Note that while the original and patched functions are specified
            -- separately, it is probably important that the lists semantically
            -- align

            , observableMemory :: [MemRegion]
            -- ^ Address ranges in the memory space of each process that should be
            --   considered observable. This can be used to specify memory-mapped
            --   I/O regions, or simply to place a focus on regions of memory
            --   that are considered of inteterest to the user.
            }
  deriving (Show)

instance Semigroup PatchData where
  (PatchData a b c d e f g) <> (PatchData a' b' c' d' e' f' g')
   = (PatchData (a <> a') (b <> b') (c <> c') (d <> d') (e <> e') (f <> f') (g <> g'))

instance Monoid PatchData where
  mempty = PatchData [] [] [] [] [] [] []

_Address :: Toml.TomlBiMap Address Toml.AnyValue
_Address = Toml._Coerce Toml._Natural

-- | This is just like the 'Toml.arrayOf' combinator, except it allows the key
-- to be elided without throwing an error. If the provided key is elided, the
-- list will be parsed as empty.
optionalArrayOf :: forall a . Toml.TomlBiMap a Toml.AnyValue -> Toml.Key -> Toml.TomlCodec [a]
optionalArrayOf codec key = Toml.Codec input output
  where
    arrCodec = Toml._Array codec

    input :: Toml.TomlEnv [a]
    input = \toml -> case DHS.lookup key (Toml.tomlPairs toml) of
      Nothing -> pure []
      Just anyVal -> Toml.whenLeftBiMapError key (Toml.backward arrCodec anyVal) pure

    output :: [a] -> Toml.TomlState [a]
    output a = do
      anyVal <- Toml.eitherToTomlState (Toml.forward arrCodec a)
      a <$ CMS.modify (Toml.insertKeyAnyVal key anyVal)

patchDataCodec :: Toml.TomlCodec PatchData
patchDataCodec = PatchData
  <$> Toml.list blockAlignmentCodec "patch-pairs" .= patchPairs
  <*> Toml.list allocationCodec "ignore-original-allocations" .= ignoreOriginalAllocations
  <*> Toml.list allocationCodec "ignore-patched-allocations" .= ignorePatchedAllocations
  <*> Toml.list equatedFunctionCodec "equated-functions" .= equatedFunctions
  <*> optionalArrayOf _Address "ignore-original-functions" .= ignoreOriginalFunctions
  <*> optionalArrayOf _Address "ignore-patched-functions" .= ignorePatchedFunctions
  <*> Toml.list memRegionCodec "observable-memory" .= observableMemory

data PatchDataParseError = UnicodeError DTEE.UnicodeException
                         | TOMLError [Toml.TomlDecodeError]
  deriving (Show)

liftExcept :: (a -> e) -> Either a b -> CME.Except e b
liftExcept injectExn e =
  case e of
    Left a -> CME.throwError (injectExn a)
    Right b -> return b

parsePatchConfig :: BS.ByteString -> Either PatchDataParseError PatchData
parsePatchConfig bs = CME.runExcept $ do
  txt <- liftExcept UnicodeError (DTE.decodeUtf8' bs)
  liftExcept TOMLError (Toml.decode patchDataCodec txt)

----------------------------------
-- Verification configuration
data VerificationConfig =
  VerificationConfig
    { cfgPairMain :: Bool
    -- ^ start by pairing the entry points of the binaries
    , cfgDiscoverFuns :: Bool
    -- ^ discover additional functions pairs during analysis
    , cfgComputeEquivalenceFrames :: Bool
    -- ^ compute fine-grained equivalence frames using heuristics
    -- if false, pre-domains will simply be computed as any possible
    -- relevant state. A failed result in this mode will fallback
    -- to attempting to use fine-grained domains.
    , cfgEmitProofs :: Bool
    -- ^ emit a structured spine of the equivalence proofs
    , cfgSolver :: PS.Solver
    -- ^ The SMT solver to use to discharge proof goals
    , cfgHeuristicTimeout :: PT.Timeout
    -- ^ The timeout to use for short heuristic queries that are allowed to fail
    -- (where there is a reasonable default)
    , cfgGoalTimeout :: PT.Timeout
    -- ^ The timeout to apply to proof goals
    , cfgGroundTimeout :: PT.Timeout
    -- ^ The timeout to use when grounding terms. We expect this to be
    -- fast and therefore a delay indicates a problem with the solver
    , cfgMacawDir :: Maybe FilePath
    -- ^ The directory to save macaw CFGs to
    , cfgSolverInteractionFile :: Maybe FilePath
    -- ^ A file to save online SMT solver interactions to
    --
    -- This only captures the interaction with the solver during symbolic
    -- execution, and not the one-off queries issued by the rest of the verifier

    , cfgVerificationMethod :: VerificationMethod
    }

data VerificationMethod
  = HoareTripleVerification
  | StrongestPostVerification
 deriving (Eq,Ord,Show)

defaultVerificationCfg :: VerificationConfig
defaultVerificationCfg =
  VerificationConfig { cfgPairMain = True
                     , cfgDiscoverFuns = True
                     , cfgComputeEquivalenceFrames = True
                     , cfgEmitProofs = True
                     , cfgSolver = PS.Yices
                     , cfgHeuristicTimeout = PT.Seconds 10
                     , cfgGoalTimeout = PT.Minutes 5
                     , cfgGroundTimeout = PT.Seconds 5
                     , cfgMacawDir = Nothing
                     , cfgSolverInteractionFile = Nothing
                     , cfgVerificationMethod = HoareTripleVerification
                     }
