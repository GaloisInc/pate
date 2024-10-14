{-|
Module           : Pate.TraceCollection
Copyright        : (c) Galois, Inc 2024
Maintainer       : Daniel Matichuk <dmatichuk@galois.com>

Specialized map that relates memory cells (see 'Pate.MemCell') and registers
to traces. Used during widening (see 'Pate.Verification.Widening') to associate
location that are widened in an equivalence domain to a trace that demonstrates
why the widening was necessary (i.e. counter-example for how that location could
be made inequivalent).

-}
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
  , insert
  , lookup
  ) where

import           Prelude hiding ( lookup )

import qualified Prettyprinter as PP

import           Data.Maybe
import qualified Data.Set as Set
import           Data.Set ( Set )

import qualified Data.Map as Map
import           Data.Map ( Map )

import qualified Data.Text as T

import qualified Data.Macaw.CFG as MM

import           Data.Parameterized.Classes()
import           Data.Parameterized.Some

import qualified Pate.Arch as PA
import           Pate.TraceTree
import qualified Pate.MemCell as PMC
import qualified Pate.Solver as PSo
import qualified Pate.Verification.StrongestPosts.CounterExample as CE

import qualified What4.JSON as W4S
import qualified Data.Aeson as JSON


-- | A map that associates locations ('MM.ArchReg' or 'PMC.MemCell') with traces
--  ('CE.TraceEvents'). Each location is mapped to a set of indexes into
--  a list of traces. These indexes are used during serialization ('W4S.W4Serializable') to
--  avoid duplication when one trace is shared by multiple locations.
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

-- | Add a new trace to the set of traces associated with the given 'MM.ArchReg'
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

-- | Add a new trace to the set of traces associated with the given 'PMC.MemCell'
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

-- | Get all traces associated with the given 'MM.ArchReg'
lookupReg ::
  PA.ValidArch arch =>
  TraceCollection sym arch ->
  MM.ArchReg arch tp ->
  [CE.TraceEvents sym arch]
lookupReg trcol reg = case Map.lookup (Some reg) (trTraceMapRegs trcol) of
  Just idxs -> map (\i -> (trAllTraces trcol) !! i) (Set.toList idxs)
  Nothing -> []

-- | Get all traces associated with the given 'PMC.MemCell'
lookupCell ::
  (PSo.ValidSym sym, PA.ValidArch arch) =>
  TraceCollection sym arch ->
  PMC.MemCell sym arch w ->
  [CE.TraceEvents sym arch]
lookupCell trcol cell = case Map.lookup (Some cell) (trTraceMapCells trcol) of
  Just idxs -> map (\i -> (trAllTraces trcol) !! i) (Set.toList idxs)
  Nothing -> []

-- | Add a single trace to the set of traces associated with the given
--  list of registers and memory locations. Note that although this
--  is functionally equivalent to folding via 'insertReg' and 'insertCell',
--  the resulting JSON from serialization (via 'W4S.W4Serializable.w4Serialize')
--  only contains one copy of the given trace.
insert ::
  PSo.ValidSym sym =>
  PA.ValidArch arch =>
  [Some (MM.ArchReg arch)] ->
  [Some (PMC.MemCell sym arch)] ->
  CE.TraceEvents sym arch ->
  TraceCollection sym arch ->
  TraceCollection sym arch
insert regs cells tr trcol = trcol
  { trAllTraces = tr:(trAllTraces trcol)
  , trTraceMapRegs =
      foldr (\reg -> Map.insertWith Set.union reg (Set.singleton idx)) (trTraceMapRegs trcol) regs
  , trTraceMapCells =
      foldr (\cell -> Map.insertWith Set.union cell (Set.singleton idx)) (trTraceMapCells trcol) cells
  }
  where
    idx = length (trAllTraces trcol)

-- | Find all traces associated with the given list of registers and memory locations
--   (i.e. each trace is associated with at least one of the given locations).
--   Traces that are associated with multiple locations (i.e. added with 'insert') only
--   occur once in the result.
lookup ::
  PSo.ValidSym sym =>
  PA.ValidArch arch =>
  [Some (MM.ArchReg arch)] ->
  [Some (PMC.MemCell sym arch)] ->
  TraceCollection sym arch ->
  [CE.TraceEvents sym arch]
lookup regs cells trcol = let
  reg_idxs = Set.unions $ map (\reg -> fromMaybe Set.empty $ Map.lookup reg (trTraceMapRegs trcol)) regs
  cell_idxs = Set.unions $ map (\cell -> fromMaybe Set.empty $ Map.lookup cell (trTraceMapCells trcol)) cells
  in map (\i -> (trAllTraces trcol) !! i) (Set.toList (Set.union reg_idxs cell_idxs))

{-
Not used a the moment, so left commented out to avoid cluttering the interface.

toList ::
  forall sym arch.
  TraceCollection sym arch ->
  [(([Some (MM.ArchReg arch)], [Some (PMC.MemCell sym arch)]), CE.TraceEvents sym arch)]
toList trcol = map go [0..(length (trAllTraces trcol))]
  where
    go :: Int -> (([Some (MM.ArchReg arch)], [Some (PMC.MemCell sym arch)]), CE.TraceEvents sym arch)
    go i = let
      tr = trAllTraces trcol !! i
      regs = Map.keys $ Map.filter (Set.member i) (trTraceMapRegs trcol)
      cells = Map.keys $ Map.filter (Set.member i) (trTraceMapCells trcol)
      in ((regs, cells), tr)

fromList ::
  forall sym arch.
  PSo.ValidSym sym =>
  PA.ValidArch arch =>
  [(([Some (MM.ArchReg arch)], [Some (PMC.MemCell sym arch)]), CE.TraceEvents sym arch)] ->
  TraceCollection sym arch
fromList trs = foldr (\((regs, cells), tr) -> insert regs cells tr) empty trs
-}

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