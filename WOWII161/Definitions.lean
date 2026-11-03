/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0.
These two definitions are copied without semantic changes from
google-deepmind/formal-conjectures, commit fd57f5d489321515f695ea205913d0ac3289f41c.
See README.md for the original paths and source correspondence.
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-! # The two graph invariants used in WOWII161 -/

@[expose] public section

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

open Finset List

/-- `Ls G` is the maximum number of leaves over all spanning trees of `G`.
It is defined to be `0` when `G` is not connected. -/
noncomputable def Ls (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  open scoped Classical in
  letI spanningTrees := { T : Subgraph G | T.IsSpanning ∧ IsTree T.coe }
  letI leaves (T : Subgraph G) := T.verts.toFinset.filter (fun v => T.degree v = 1)
  letI num_leaves (T : Subgraph G) := (leaves T).card
  sSup (Set.image (fun T => (num_leaves T : ℝ)) spanningTrees)
 
/-- Maximum local independence number over all vertices. -/
noncomputable def maxLocalIndependence (G : SimpleGraph α) : ℕ :=
  let locals := Finset.univ.image (fun v => (G.induce (G.neighborSet v)).indepNum)
  (locals.max).getD 0

end SimpleGraph

