
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Pate.TraceCollection
  ( TraceCollection
  , empty
  , lookupReg
  , insertReg
  , lookupCell
  , insertCell
  ) where

import           Prelude hiding ( lookup )

import qualified Prettyprinter as PP

import qualified Data.Set as Set
import           Data.Set ( Set )

import qualified Data.Map as Map
import           Data.Map ( Map )

import qualified Data.Text as T

import qualified Data.Macaw.CFG as MM

import           Data.Parameterized.Classes
import           Data.Parameterized.Some

import qualified Pate.Arch as PA
import           Pate.TraceTree
import qualified Pate.MemCell as PMC
import qualified Pate.Solver as PSo
import qualified Pate.Verification.StrongestPosts.CounterExample as CE

import qualified What4.JSON as W4S
import qualified Data.Aeson as JSON

data TraceCollection sym arch = TraceCollection
  { 
    trAllTraces :: [CE.TraceEvents sym arch]
  , trTraceMapRegs :: Map (Some (MM.ArchReg arch)) (Set Int)
  -- ^ mapping from registers into indexes in to the list of all traces
  , trTraceMapCells :: Map (Some (PMC.MemCell sym arch)) (Set Int)
  -- ^ mapping from memory cells into indexes in to the list of all traces
  }

empty :: TraceCollection sym arch
empty = TraceCollection [] Map.empty Map.empty

insertReg ::
  PA.ValidArch arch =>
  MM.ArchReg arch tp ->
  CE.TraceEvents sym arch ->
  TraceCollection sym arch ->
  TraceCollection sym arch
insertReg reg tr trcol = trcol 
  { trAllTraces = tr:(trAllTraces trcol)
  , trTraceMapRegs = Map.insertWith Set.union (Some reg) (Set.singleton (length (trAllTraces trcol))) (trTraceMapRegs trcol)
  }

insertCell ::
  PSo.ValidSym sym =>
  PMC.MemCell sym arch w ->
  CE.TraceEvents sym arch ->
  TraceCollection sym arch ->
  TraceCollection sym arch
insertCell cell tr trcol = trcol 
  { trAllTraces = tr:(trAllTraces trcol)
  , trTraceMapCells = Map.insertWith Set.union (Some cell) (Set.singleton (length (trAllTraces trcol))) (trTraceMapCells trcol)
  }

lookupReg ::
  PA.ValidArch arch =>
  TraceCollection sym arch ->
  MM.ArchReg arch tp ->
  [CE.TraceEvents sym arch]
lookupReg trcol reg = case Map.lookup (Some reg) (trTraceMapRegs trcol) of
  Just idxs -> map (\i -> (trAllTraces trcol) !! i) (Set.toList idxs)
  Nothing -> []

lookupCell ::
  (PSo.ValidSym sym, PA.ValidArch arch) =>
  TraceCollection sym arch ->
  PMC.MemCell sym arch w ->
  [CE.TraceEvents sym arch]
lookupCell trcol cell = case Map.lookup (Some cell) (trTraceMapCells trcol) of
  Just idxs -> map (\i -> (trAllTraces trcol) !! i) (Set.toList idxs)
  Nothing -> []

instance (PA.ValidArch arch, PSo.ValidSym sym) => W4S.W4Serializable sym (TraceCollection sym arch) where
  w4Serialize (TraceCollection allTraces regs cells) = do
    W4S.object 
      [ "all_traces" W4S..= allTraces
      , "trace_map_regs" W4S..= regs
      , "trace_map_cells" W4S..= cells
      ]

instance forall sym arch. (PA.ValidArch arch, PSo.ValidSym sym) => IsTraceNode '(sym,arch) "trace_collection" where
  type TraceNodeType '(sym,arch) "trace_collection" = TraceCollection sym arch
  type TraceNodeLabel "trace_collection" = T.Text

  prettyNode nm _tc = "Trace Collection: " <> PP.pretty nm
  nodeTags = mkTags @'(sym,arch) @"trace_collection" [Summary, Simplified]
  jsonNode sym lbl v = do
    v_json <- W4S.w4ToJSON sym v
    return $ JSON.object [ "name"  JSON..= lbl , "trace_collection" JSON..= v_json  ]