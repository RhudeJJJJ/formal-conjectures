/-
Copyright 2026 The Formal Conjectures Authors.
Modified 4 November 2026: standalone Palomar statement/proof port; mathematical definitions retained.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-! Definitions copied from the exact PR7385 statement.
Only the unused admitted target declarations and repository metadata attributes are omitted. -/

@[expose] public section
namespace PHOEG.GraphicalBell
open Finset SimpleGraph

/-- An actual partition into nonempty independent blocks, counted without labels. -/
def IsStablePartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ B ∈ P, B.Nonempty ∧ G.IsIndepSet (B : Set V)) ∧
  (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) ∧ P.biUnion id = univ

noncomputable def stirling {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card {P : Finset (Finset V) // IsStablePartition G P ∧ P.card = k}

noncomputable def bell {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  Nat.card {P : Finset (Finset V) // IsStablePartition G P}

def cliqueOrder (n m : ℕ) : ℕ := Nat.findGreatest (fun q => q.choose 2 ≤ m) n

/-- A clique, a vertex with the residual number of clique neighbors, and isolates.
At maximum feasible size the extra vertex is absent. -/
def quasiComplete (n m : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧
    ((u.val < cliqueOrder n m ∧ v.val < cliqueOrder n m) ∨
      (u.val = cliqueOrder n m ∧ v.val < m - (cliqueOrder n m).choose 2) ∨
      (v.val = cliqueOrder n m ∧ u.val < m - (cliqueOrder n m).choose 2))
  symm := ⟨by
    intro u v h
    constructor
    · exact Ne.symm h.1
    · rcases h.2 with h | h | h
      · exact Or.inl ⟨h.2, h.1⟩
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

end PHOEG.GraphicalBell
