{-# LANGUAGE RankNTypes #-}
module Interactive.Render.BlockPairDetail (
  renderBlockPairDetail
  ) where

import           Control.Lens ( (^.) )
import qualified Control.Lens as L
import qualified Data.Foldable as F
import           Data.Maybe ( fromMaybe )
import qualified Data.String.UTF8 as UTF8
import           Graphics.UI.Threepenny ( (#), (#+), (#.) )
import qualified Graphics.UI.Threepenny as TP
import qualified Language.C as LC

import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MC

import qualified Pate.Arch as PA
import qualified Pate.Binary as PB
import qualified Pate.Event as PE
import qualified Pate.Proof.Instances as PFI
import qualified Pate.Types as PT

import qualified Interactive.Render.SliceGraph as IRS
import qualified Interactive.State as IS

renderCounterexample :: PE.EquivalenceResult arch -> [TP.UI TP.Element]
renderCounterexample er =
  case er of
    PE.Equivalent -> []
    PE.Inconclusive -> []
    PE.Inequivalent ir ->
          [TP.ul #+ [ TP.li #+ [ TP.string ("Reason: " ++ show (PFI.ineqReason ir))
                               , TP.pre #+ [TP.string (PFI.ppInequivalencePreRegs ir)]
                               ]
                   ]
          ]

-- | Note that we always look up the original address because we key the
-- function name off of that... we could do better
renderSource :: (PA.ArchConstraints arch)
             => IS.State arch
             -> (IS.SourcePair LC.CTranslUnit -> LC.CTranslUnit)
             -> L.Getter (IS.State arch) (Maybe (PB.LoadedELF arch, b))
             -> MC.MemAddr (MC.ArchAddrWidth arch)
             -> [TP.UI TP.Element]
renderSource st getSource binL addr = fromMaybe [] $ do
  (lelf, _) <- st ^. binL
  bname <- MBL.symbolFor (PB.loadedBinary lelf) addr
  let sname = UTF8.toString (UTF8.fromRep bname)
  LC.CTranslUnit decls _ <- getSource <$> st ^. IS.sources
  fundef <- F.find (matchingFunctionName sname) decls
  return [ TP.code #+ [ TP.pre # TP.set TP.text (show (LC.pretty fundef)) #. "source-listing" ] ]

-- | Find the declaration matching the given function name
matchingFunctionName :: String -> LC.CExternalDeclaration LC.NodeInfo -> Bool
matchingFunctionName sname def =
  case def of
    LC.CDeclExt {} -> False
    LC.CAsmExt {} -> False
    LC.CFDefExt (LC.CFunDef _declspecs declr _decls _stmts _annot) ->
      case declr of
        LC.CDeclr (Just ident) _ _ _ _ -> LC.identToString ident == sname
        LC.CDeclr Nothing _ _ _ _ -> False

renderFunctionName :: (PA.ArchConstraints arch)
                   => IS.State arch
                   -> MC.MemAddr (MC.ArchAddrWidth arch)
                   -> [TP.UI TP.Element]
renderFunctionName st origAddr = fromMaybe [] $ do
  (lelf, _) <- st ^. IS.originalBinary
  bname <- MBL.symbolFor (PB.loadedBinary lelf) origAddr
  let sname = UTF8.toString (UTF8.fromRep bname)
  return [TP.string ("(Function: " ++ sname ++ ")")]

renderAddr :: (Show a) => String -> a -> TP.UI TP.Element
renderAddr label addr = TP.string (label ++ " (" ++ show addr ++ ")")

renderBlockPairDetail
  :: (PA.ArchConstraints arch)
  => IS.State arch
  -> PE.Blocks arch PT.Original
  -> PE.Blocks arch PT.Patched
  -> Maybe (PE.EquivalenceResult arch)
  -> TP.UI (TP.Element, TP.UI (), TP.UI ())
renderBlockPairDetail st o@(PE.Blocks blkO _opbs) p@(PE.Blocks blkP _ppbs) res = do
  g <- TP.grid [ maybe [] renderCounterexample res
               , concat [[renderAddr "Original Code" origAddr, renderAddr "Patched Code" patchedAddr], renderFunctionName st origAddr]
               , concat [ renderSource st IS.originalSource IS.originalBinary origAddr
                        , renderSource st IS.patchedSource IS.patchedBinary patchedAddr
                        ]
               , [origGraphDiv, patchedGraphDiv]
               ]
  return (g, origGraphSetup, patchedGraphSetup)
  where
    origAddr = PT.blockMemAddr blkO
    patchedAddr = PT.blockMemAddr blkP
    (origGraphDiv, origGraphSetup) = IRS.renderSliceGraph "original-slice-graph" o
    (patchedGraphDiv, patchedGraphSetup) = IRS.renderSliceGraph "patched-slice-graph" p
