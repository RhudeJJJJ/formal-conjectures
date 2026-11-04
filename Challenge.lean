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

/-!
# Fixed-order, fixed-size graphical Stirling and Bell minimum

For a finite simple graph G, stirling G k counts the partitions of the entire
vertex set into exactly k nonempty independent, unlabeled blocks. bell G counts
all such stable partitions. With n vertices and m edges, quasiComplete n m is
a maximal clique, a residual vertex joined to the first residual clique
vertices, and the other isolated vertices. The extra vertex is absent when the
clique already uses every vertex.

The two recorded theorems state that Q(n,m) minimizes each stable-partition
count, and hence the total count, among all graphs with those n and m. The
domain is n >= 1, with arbitrary finite vertex types and explicit decidability
instances; k is any natural number. Disconnected graphs are included. There is
no comparison of ordinary monomial coefficients, uniqueness classification,
connected-only claim, or first-priority claim.

Source: PHOEG CSD8 presentation, displayed slides29-31:
https://orbi.umons.ac.be/bitstream/20.500.12907/7470/1/Hauweele_CSD8.pdf
Author manuscript: J.J.Gebendorfer, The Quasi-Complete Graph Minimizes Graphical
Stirling Numbers at Fixed Order and Size,25July2026, archived with the source
comparison at https://github.com/user-attachments/files/33356610/Gebendorfer_Graphical_Bell_Submission_Package_2026.zip

This is the full coefficientwise statement followed by its Bell consequence,
matching the mathematical types proposed in formal-conjectures PR7385. The
source development is ported from its immutable Lean4.33.1 certificate to the
toolchain and Mathlib recorded here. Automation and prior audit boundaries are
disclosed in formalization.yaml and README.md. Novelty and independent human
peer review are not established by this registration project.
-/

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

namespace PHOEG.GraphicalBell
open SimpleGraph

/-- Each fixed nonempty independent-block count is minimized by Q(n,m). -/
theorem full_coefficientwise {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (_hn : 1 <= Fintype.card V) (k : Nat) :
    stirling (quasiComplete (Fintype.card V) G.edgeFinset.card) k <= stirling G k := by
  sorry

/-- Summing all stable-block counts gives the graphical Bell minimum. -/
theorem full_conjecture {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hn : 1 <= Fintype.card V) :
    bell (quasiComplete (Fintype.card V) G.edgeFinset.card) <= bell G := by
  sorry

end PHOEG.GraphicalBell
