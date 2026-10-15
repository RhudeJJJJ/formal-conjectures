/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Independence
import Mathlib.Tactic

/-! WOWII 422d-U, the explicitly reconstructed upper reading with NONPROPER
closed-neighborhood containment. Gebendorfer's 7 September 2026 witness.
OpenAI Codex assisted with formalization. No historical-glyph recovery claimed. -/
namespace WOWII422dProof
open SimpleGraph Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def adjacency : Fin 12 → Finset (Fin 12) := ![{2,3,4,5,6,7},{2,3,4,5,6,7},{0,1,8,9,10,11},{0,1,8,9,10,11},{0,1,5},{0,1,4},{0,1,7},{0,1,6},{2,3,9},{2,3,8},{2,3,11},{2,3,10}]
def witness : SimpleGraph (Fin 12) where
  Adj u v := v ∈ adjacency u
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
instance : DecidableRel witness.Adj := inferInstanceAs
  (DecidableRel fun u v : Fin 12 => v ∈ adjacency u)

def parent : Fin 12 → Fin 12 := ![0,2,0,0,0,0,0,0,2,2,2,2]
lemma parent_adj : ∀ v : Fin 12, v ≠ 0 → witness.Adj v (parent v) := by decide
lemma parent_depth : ∀ v : Fin 12, parent v = 0 ∨ parent v = 2 := by decide
lemma root_reachable (v : Fin 12) : witness.Reachable v 0 := by
  by_cases h : v = 0
  · subst v; exact .refl _
  have he := (parent_adj v h).reachable
  rcases parent_depth v with hp | hp
  · simpa only [hp] using he
  · exact he.trans (hp ▸ (show witness.Adj (2 : Fin 12) 0 by decide).reachable)
theorem witness_connected : witness.Connected :=
  ⟨fun u v => (root_reachable u).trans (root_reachable v).symm⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
def containingVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ u, u ≠ v ∧ ∀ w,
    (w = u ∨ G.Adj u w) → (w = v ∨ G.Adj v w)
def edgesOn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ S).card
noncomputable def bound (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.induce ((univ \ containingVertices G : Finset V) : Set V)).indepNum +
    (edgesOn G (containingVertices G) + 1) / 3

lemma containing_spec : containingVertices witness = {4,5,6,7,8,9,10,11} := by decide
lemma induced_edges : edgesOn witness (containingVertices witness) = 4 := by decide
lemma residual_independence :
    (witness.induce ((univ \ containingVertices witness : Finset (Fin 12)) : Set (Fin 12))).indepNum = 2 := by
  rw [containing_spec, indep_num_eq_computable]
  decide
lemma bound_eq : bound witness = 3 := by
  rw [bound, residual_independence, induced_edges]

/-- Exhaustive finite certificate over all 4096 candidate vertex sets. -/
lemma independent_dominating_lower : ∀ D : Finset (Fin 12),
    ((∀ u ∈ D, ∀ v ∈ D, u ≠ v → ¬witness.Adj u v) ∧
      (∀ v, v ∈ D ∨ ∃ w ∈ D, witness.Adj v w)) → 4 ≤ D.card := by decide

def selected : Finset (Fin 12) := {0,1,8,10}
lemma selected_certificate : witness.IsIndepDominating (selected : Set (Fin 12)) ∧
    selected.card = 4 := by
  constructor
  · change (∀ u ∈ selected, ∀ v ∈ selected, u ≠ v → ¬witness.Adj u v) ∧
      (∀ v, v ∈ selected ∨ ∃ w ∈ selected, witness.Adj v w)
    decide
  · decide

theorem independent_domination_eq : witness.indepDominationNumber = 4 := by
  apply Nat.le_antisymm
  · exact Nat.sInf_le ⟨selected, selected_certificate.1.1, selected_certificate.1.2,
      selected_certificate.2⟩
  · apply le_csInf
    · exact ⟨4, selected, selected_certificate.1.1, selected_certificate.1.2,
        selected_certificate.2⟩
    · rintro n ⟨D,hD⟩
      rw [← hD.card_eq]
      exact independent_dominating_lower D ⟨hD.isIndep, hD.isDominating⟩

theorem conjecture422d_upper : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card W →
      G.indepDominationNumber ≤ bound G := by
  intro h
  have hh := h (Fin 12) witness witness_connected (by decide)
  rw [independent_domination_eq, bound_eq] at hh
  omega

#print axioms witness_connected
#print axioms independent_domination_eq
#print axioms conjecture422d_upper
end WOWII422dProof
