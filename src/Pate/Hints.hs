{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
-- | This module defines a data type to represent the types of advisory information that the
-- pate system can accept.
--
-- The types of information we are interested in include:
--
-- * Address mappings from original to patched blocks
--
-- * Code discovery hints (e.g., function entry points)
--
-- Note that the parsers for data sources are delegated to the binary so that we
-- don't impose any additional dependencies on the core verifier.
module Pate.Hints (
  SymbolExtent(..),
  FunctionDescriptor(..),
  VerificationHints(..),
  HintValidationFailure(..),
  validate,
  ValidVerificationHints(..),
  Hinted(..)
  ) where

import qualified Control.DeepSeq as CD
import           Control.Lens ( (^.), (%=) )
import qualified Control.Lens as L
import qualified Control.Monad.State.Strict as CMS
import qualified Data.Foldable as F
import qualified Data.IntervalMap.Strict as DIS
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import           Data.Word ( Word32, Word64 )
import           GHC.Generics ( Generic )
import           Numeric ( showHex )
import qualified Prettyprinter as PP


-- | A wrapper to carry 'VerificationHints' with another object (e.g., the associated binary)
data Hinted a = Hinted { hints :: VerificationHints
                       , hinted :: a
                       }

-- | The address and size of memory referenced by a symbol
data SymbolExtent =
  SymbolExtent { symbolLocation :: Word64
               , symbolSize :: Word32
               }
  deriving (Read, Show, Eq, Ord, Generic)

instance CD.NFData SymbolExtent

instance PP.Pretty SymbolExtent where
  pretty symExt = PP.brackets (ppHex (symbolLocation symExt) <> PP.pretty ":" <> PP.pretty (symbolSize symExt))

data FunctionDescriptor =
  FunctionDescriptor { functionSymbol :: T.Text
                     , functionAddress :: Word64
                     , functionArguments :: [T.Text]
                     -- ^ Names of function arguments; FIXME: Will eventually
                     -- need type annotations. For now, assume all arguments are
                     -- ints
                     }
  deriving (Read, Show, Generic, Eq, Ord)

instance CD.NFData FunctionDescriptor

-- | The user-facing structure for defining the hints supported by the pate tools
--
-- Parsers generate these, which are then combined and validated with the
-- 'validate' function.  The 'ValidVerificationHints' are used in the verifier.
data VerificationHints =
  VerificationHints { blockMappings :: [(Word64, Word64)]
                    -- ^ A mapping from original block addresses to their
                    -- corresponding address in the patched binary
                    , functionEntries :: [(T.Text, FunctionDescriptor)]
                    -- ^ Addresses of function entry points (along with corresponding symbol names)
                    --
                    -- Note that symbols are assumed to be representable as
                    -- 'T.Text'; non-conforming symbols will be rejected
                    , dataSymbols :: [(T.Text, SymbolExtent)]
                    -- ^ Boundaries of data values
                    }
  deriving (Read, Show, Generic, Eq)

instance CD.NFData VerificationHints

emptyVerificationHints :: VerificationHints
emptyVerificationHints =
  VerificationHints { blockMappings = mempty
                    , functionEntries = mempty
                    , dataSymbols = mempty
                    }

mergeHints :: VerificationHints -> VerificationHints -> VerificationHints
mergeHints h1 h2 =
  VerificationHints { blockMappings = blockMappings h1 <> blockMappings h2
                    , functionEntries = functionEntries h1 <> functionEntries h2
                    , dataSymbols = dataSymbols h1 <> dataSymbols h2
                    }

-- | Data errors that are reported during validation (see 'validate')
data HintValidationFailure = DuplicateBlockMapping Word64 Word64 Word64
                           | DuplicateFunctionName T.Text Word64 Word64
                           | DuplicateSymbolName T.Text Word64 Word64
                           | OverlappingSymbolExtent T.Text [SymbolExtent] SymbolExtent
                           deriving (Show)

ppHex :: (Integral a, Show a) => a -> PP.Doc ann
ppHex a = PP.pretty "0x" <> PP.pretty (showHex a "")

instance PP.Pretty HintValidationFailure where
  pretty hvf =
    case hvf of
      DuplicateBlockMapping origAddr firstPatchedAddr thisPatchedAddr ->
        mconcat [ PP.pretty "Duplicate address mapping for basic block: "
                , ppHex origAddr
                , PP.pretty " had mapped to "
                , ppHex firstPatchedAddr
                , PP.pretty ", which conflicts with "
                , ppHex thisPatchedAddr
                ]
      DuplicateFunctionName name prevAddr thisAddr ->
        mconcat [ PP.pretty "Function name '"
                , PP.pretty name
                , PP.pretty "' assigned to two different addresses (originally "
                , ppHex prevAddr
                , PP.pretty ") and then "
                , ppHex thisAddr
                ]
      DuplicateSymbolName name prevAddr thisAddr ->
        mconcat [ PP.pretty "Data symbol name "
                , PP.dquotes (PP.pretty name)
                , PP.pretty " assigned to two different addresses (originally "
                , ppHex prevAddr
                , PP.pretty ") and then "
                , ppHex thisAddr
                ]
      OverlappingSymbolExtent name overlapping ext ->
        mconcat [ PP.pretty "Data symbol "
                , PP.dquotes (PP.pretty name)
                , PP.pretty " assigned an address and size that overlaps other extents "
                , PP.pretty overlapping
                , PP.pretty " at extent "
                , PP.pretty ext
                ]

data State =
  State { _sValidation :: Seq.Seq HintValidationFailure
        -- ^ Accumulated validation errors
        , _sBlockMap :: Map.Map Word64 Word64
        -- ^ It is an error to have the same block mapped to two different addresses
        --
        -- We could in principle support that, but various things (including
        -- this check) would need to change
        , _sFunctionMap :: Map.Map T.Text Word64
        -- ^ It is an error to assign two different addresses to the same symbol name
        , _sSymbolExtents :: DIS.IntervalMap Word64 (T.Text, SymbolExtent)
        -- ^ It is an error for symbol extents to overlap
        , _sSymbolMap :: Map.Map T.Text SymbolExtent
        -- ^ It is an error for the same name to be assigned to two different extents
        }

L.makeLenses ''State

emptyState :: State
emptyState = State { _sValidation = mempty
                   , _sBlockMap = mempty
                   , _sFunctionMap = mempty
                   , _sSymbolExtents = mempty
                   , _sSymbolMap = mempty
                   }

newtype Validator a = Validator { unValidator :: CMS.State State a }
  deriving ( Functor
           , Applicative
           , Monad
           , CMS.MonadState State
           )

instance Semigroup VerificationHints where
  (<>) = mergeHints

instance Monoid VerificationHints where
  mempty = emptyVerificationHints

-- | Verification hints that have been validated to ensure there are no inconsistencies
--
-- See the 'validate' function for the validation rules
data ValidVerificationHints =
  ValidVerificationHints { validBlockMappings :: Map.Map Word64 Word64
                         -- ^ A map from original block address to its location in the patched binary
                         , validFunctionEntries :: Map.Map T.Text Word64
                         -- ^ A map from symbol names to addresses
                         --
                         -- These are addresses in the original binary (which
                         -- can be translated as-needed by consulting
                         -- 'validBlockMappings' to account for any changes in
                         -- the layout of the patched binary)
                         , validDataSymbols :: Map.Map T.Text SymbolExtent
                         -- ^ Locations and sizes of variables
                         --
                         -- These must not overlap
                         }
  deriving (Show)

addBlockMapping :: (Word64, Word64) -> Validator ()
addBlockMapping (origAddr, patchedAddr) = do
  bm <- CMS.gets _sBlockMap
  case Map.lookup origAddr bm of
    Nothing -> sBlockMap %= Map.insert origAddr patchedAddr
    Just mappedAddr -> do
      let msg = DuplicateBlockMapping origAddr mappedAddr patchedAddr
      sValidation %= (Seq.|> msg)

addFunctionEntry :: (T.Text, FunctionDescriptor) -> Validator ()
addFunctionEntry (name, fd) = do
  fm <- CMS.gets _sFunctionMap
  let addr = functionAddress fd
  case Map.lookup name fm of
    Nothing -> sFunctionMap %= Map.insert name addr
    Just oldAddr -> do
      let msg = DuplicateFunctionName name oldAddr addr
      sValidation %= (Seq.|> msg)

addDataSymbol :: (T.Text, SymbolExtent) -> Validator ()
addDataSymbol (name, ext) = do
  exts <- CMS.gets _sSymbolExtents
  syms <- CMS.gets _sSymbolMap

  case Map.lookup name syms of
    Nothing -> sSymbolMap %= Map.insert name ext
    Just prevExt -> do
      let msg = DuplicateSymbolName name (symbolLocation prevExt) (symbolLocation ext)
      sValidation %= (Seq.|> msg)

  let key = DIS.IntervalCO (symbolLocation ext) (symbolLocation ext + fromIntegral (symbolSize ext))
  let overlaps = DIS.intersecting exts key
  if | DIS.null overlaps -> sSymbolExtents %= DIS.insert key (name, ext)
     | otherwise -> do
         let msg = OverlappingSymbolExtent name (fmap snd (DIS.elems overlaps)) ext
         sValidation %= (Seq.|> msg)


doValidation :: VerificationHints -> Validator ()
doValidation vh = do
  mapM_ addBlockMapping (blockMappings vh)
  mapM_ addFunctionEntry (functionEntries vh)
  mapM_ addDataSymbol (dataSymbols vh)


-- | Validate a raw set of 'VerificationHints'
--
-- This verifies that there are no conflicting entries (e.g., two different
-- addresses for the same symbol)
--
-- If there are validation errors, they are collected and reported.  Invalid
-- entries are discarded to allow analysis to continue (the first entry in a
-- conflict is taken).
validate :: VerificationHints -> (ValidVerificationHints, [HintValidationFailure])
validate vh =
  (v, F.toList (finalState ^. sValidation))
  where
    finalState = CMS.execState (unValidator (doValidation vh)) emptyState
    v = ValidVerificationHints { validBlockMappings = finalState ^. sBlockMap
                               , validFunctionEntries = finalState ^. sFunctionMap
                               , validDataSymbols = finalState ^. sSymbolMap
                               }
