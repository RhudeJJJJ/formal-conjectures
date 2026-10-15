/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic

/-!
# WOWII 364: the explicitly transcribed half-edge version

P4 is the earlier public counterexample credited to Siddhant Dubey in issue 7275.
The supplied Gebendorfer manuscript also gives an unbounded family and a distinct
bracketed repair. Neither of those additional universal statements is proved here.
OpenAI Codex assisted with formalization.
-/
namespace WOWII364Proof
open SimpleGraph Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def witness : SimpleGraph (Fin 4) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro u h; omega⟩
instance : DecidableRel witness.Adj := inferInstanceAs
  (DecidableRel fun u v : Fin 4 => u.val + 1 = v.val ∨ v.val + 1 = u.val)

def supports {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∃ w, G.degree w = 1 ∧ G.Adj v w

def degreeTwo {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Finset V := univ.filter fun v => G.degree v = 2

def edgesOn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ S).card

def bound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℚ :=
  ((supports G).card : ℚ) + (edgesOn G (degreeTwo G) : ℚ) / 2

lemma witness_connected : witness.Connected := by
  have h01 : witness.Adj 0 1 := by decide
  have h12 : witness.Adj 1 2 := by decide
  have h23 : witness.Adj 2 3 := by decide
  have hr : ∀ v : Fin 4, witness.Reachable 0 v := by
    intro v
    fin_cases v
    · exact .refl _
    · exact h01.reachable
    · exact h01.reachable.trans h12.reachable
    · exact (h01.reachable.trans h12.reachable).trans h23.reachable
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

lemma witness_tree : witness.IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨witness_connected, ?_⟩
  have he : witness.edgeFinset.card = 3 := by decide
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, he,
    Nat.card_eq_fintype_card]
  decide

lemma supports_eq : supports witness = {1, 2} := by decide
lemma supports_card : (supports witness).card = 2 := by rw [supports_eq]; decide
lemma degreeTwo_eq : degreeTwo witness = {1, 2} := by decide
lemma edge_count : edgesOn witness (degreeTwo witness) = 1 := by decide
lemma bound_eq : bound witness = 5 / 2 := by
  rw [bound, supports_card, edge_count]
  norm_num

def selected : Finset (Fin 4) := {1, 2}
lemma selected_total : witness.IsTotalDominating (selected : Set (Fin 4)) := by
  change ∀ v : Fin 4, ∃ w ∈ selected, witness.Adj v w
  decide
lemma total_upper : witness.totalDominationNumber ≤ 2 :=
  Nat.sInf_le ⟨selected, selected_total, by decide⟩

lemma total_lower : 2 ≤ witness.totalDominationNumber := by
  have he : ∀ D : Finset (Fin 4),
      (∀ v : Fin 4, ∃ w ∈ D, witness.Adj v w) → 2 ≤ D.card := by decide
  apply le_csInf
  · exact ⟨2, selected, selected_total, by decide⟩
  · rintro n ⟨D, hD⟩
    rw [← hD.card_eq]
    exact he D hD.isTotalDominating

lemma total_eq : witness.totalDominationNumber = 2 := le_antisymm total_upper total_lower

/-- The full universal half-edge statement is false. -/
theorem conjecture364 : ¬ ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], G.IsTree → 2 < Fintype.card V →
      bound G ≤ G.totalDominationNumber := by
  intro h
  have hb := h (Fin 4) witness witness_tree (by decide)
  rw [bound_eq, total_eq] at hb
  norm_num at hb

/-- The P4 witness satisfies the distinct bracketed strengthened bound. -/
lemma bracket_control :
    (⌈(((supports witness).card : ℚ) + edgesOn witness (degreeTwo witness) + 1) / 2⌉₊) =
      witness.totalDominationNumber := by
  rw [supports_card, edge_count, total_eq]
  norm_num

#print axioms conjecture364
#print axioms total_eq
#print axioms bracket_control
end WOWII364Proof
