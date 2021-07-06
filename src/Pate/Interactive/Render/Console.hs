{-# LANGUAGE GADTs #-}
module Pate.Interactive.Render.Console (
  renderConsole
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad ( void )
import           Control.Monad.IO.Class ( liftIO )
import qualified Data.IORef as IOR
import           Data.Parameterized.Some ( Some(..) )
import           Graphics.UI.Threepenny ( (#), (#+), (#.) )
import qualified Graphics.UI.Threepenny as TP

import qualified Pate.Arch as PA
import qualified Pate.Binary as PBi
import qualified Pate.Block as PB
import qualified Pate.Event as PE
import qualified Pate.PatchPair as PPa
import qualified Pate.Proof as PPr
import qualified Pate.Proof.Instances as PFI

import qualified Pate.Interactive.Render.BlockPairDetail as IRB
import qualified Pate.Interactive.State as IS

-- | Show the original block at the given address (as well as its corresponding patched block)
--
-- Note that the totally unconstrained argument is the data payload passed in by
-- the event handler (e.g., click event), which is not used.
showBlockPairDetail :: (PA.ArchConstraints arch)
                    => IS.State arch
                    -> TP.Element
                    -> PE.Blocks arch PBi.Original
                    -> PE.Blocks arch PBi.Patched
                    -> Maybe (PE.EquivalenceResult arch)
                    -> a
                    -> TP.UI ()
showBlockPairDetail st detailDiv o p res _ = do
  (g, origGraphSetup, patchedGraphSetup) <- IRB.renderBlockPairDetail st o p res
  void $ return detailDiv # TP.set TP.children [g]

  -- Call the remote functions to set up the graph in the relevant divs
  origGraphSetup
  patchedGraphSetup
  -- Make sure the call to set up the graph is flushed to the client
  TP.flushCallBuffer

renderEquivalenceResult :: PE.EquivalenceResult arch -> TP.UI TP.Element
renderEquivalenceResult res =
  case res of
    PE.Equivalent -> TP.span #+ [ TP.string "["
                                , TP.string "✓" #. "sat-equivalent"
                                , TP.string "]"
                                ]
    PE.Inconclusive -> TP.span #+ [ TP.string "["
                                , TP.string "?" #. "sat-indeterminate"
                                , TP.string "]"
                                ]
    PE.Inequivalent _mdl -> TP.span #+ [ TP.string "["
                                       , TP.string "✗" #. "sat-inequivalent"
                                       , TP.string "]"
                                       ]

verificationStatusTag :: PPr.VerificationStatus ce -> String
verificationStatusTag vs =
  case vs of
    PPr.Unverified -> "Unverified"
    PPr.VerificationSkipped -> "Skipped"
    PPr.VerificationSuccess -> "Verified"
    PPr.VerificationFail _ -> "Failed"

renderProofApp
  :: PPr.ProofApp prf node tp
  -> TP.UI TP.Element
renderProofApp app =
  case app of
    PPr.ProofBlockSlice {} -> TP.string "ProofBlockSlice"
    PPr.ProofFunctionCall {} -> TP.string "ProofFunctionCall"
    PPr.ProofTriple {} -> TP.string "ProofTriple"
    PPr.ProofStatus vs -> TP.string ("ProofStatus=" ++ verificationStatusTag vs)
    PPr.ProofDomain {} -> TP.string "ProofDomain"

renderEvent :: (PA.ArchConstraints arch) => IS.State arch -> TP.Element -> PE.Event arch -> TP.UI TP.Element
renderEvent st detailDiv evt =
  case evt of
    PE.LoadedBinaries {} -> TP.string "Loaded original and patched binaries"
    PE.ElfLoaderWarnings pes ->
      TP.ul #+ (map (\w -> TP.li #+ [TP.string (show w)]) pes)
    PE.CheckedEquivalence (PPa.PatchPair ob@(PE.Blocks blkO _) pb@(PE.Blocks blkP _)) res duration -> do
      let
        origAddr = PB.blockMemAddr blkO
        patchedAddr = PB.blockMemAddr blkP
      blockLink <- TP.a # TP.set TP.text (show origAddr)
                        # TP.set TP.href ("#" ++ show origAddr)
      TP.on TP.click blockLink (showBlockPairDetail st detailDiv ob pb (Just res))
      TP.span #+ [ TP.string "Checking original block at "
                 , return blockLink
                 , TP.string " against patched block at "
                 , TP.string (show patchedAddr)
                 , TP.string (" (in " ++ show duration ++ ")")
                 , renderEquivalenceResult res
                 ]
    PE.ProofIntermediate (PPa.PatchPair ob@(PE.Blocks blkO _) pb@(PE.Blocks _blkP _))
                         (PFI.SomeProofSym _ (PPr.ProofNonceExpr nonce (Some parentNonce) app)) duration -> do
      let origAddr = PB.blockMemAddr blkO
      blockLink <- TP.a # TP.set TP.text (show origAddr)
                        # TP.set TP.href ("#" ++ show origAddr)
      TP.on TP.click blockLink (showBlockPairDetail st detailDiv ob pb Nothing)
      TP.span #+ [ TP.string "Verified an intermediate proof node ("
                 , TP.string (show (PPr.proofNonceValue nonce) ++ "->" ++ show (PPr.proofNonceValue parentNonce))
                 , TP.string ") for "
                 , return blockLink
                 , TP.string ": "
                 , renderProofApp app
                 , TP.string (" (in " ++ show duration ++ ")")
                 ]
    PE.ProvenGoal _bp _ _ -> do
      TP.span #+ [ TP.string "Verified all goals" ]
    _ -> TP.string ""

-- | Render the most recent events
--
-- The most recent event will be on the bottom (as in a normal scrolling
-- terminal), which requires us to reverse the events list
renderConsole :: (PA.ArchConstraints arch)
              => IS.StateRef arch
              -> TP.Element
              -> TP.UI TP.Element
renderConsole r detailDiv = do
  state <- liftIO $ IOR.readIORef (IS.stateRef r)
  TP.ul #+ (map (\evt -> TP.li #+ [renderEvent state detailDiv evt]) (reverse (state ^. IS.recentEvents)))
