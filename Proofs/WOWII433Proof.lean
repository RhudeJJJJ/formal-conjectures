/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import Mathlib.Tactic

/-! The explicit maximum-degree / upper-bound reading WOWII 433-M.
The primary row has a missing sign and a P/M mismatch. No historical intent
is recovered here. Source: Gebendorfer, 6 September 2026, issue 7274.
OpenAI Codex assisted with formalization. -/
namespace WOWII433Proof
open SimpleGraph Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def adjacency : Fin 52 → Finset (Fin 52) := ![{1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,25,26,27,43,44,45,49,50,51},{0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,28,29,30,46,47,48},{0,1,3,4,5,6,7,8,9,10,11,12,16,17,18,19,20,21,31,32,33,49,50,51},{0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,19,20,21,22,23,24,34,35,36},{0,1,2,3,5,6,7,8,9,10,11,12,16,17,18,22,23,24,25,26,27,37,38,39},{0,1,2,3,4,6,7,8,9,10,11,12,19,20,21,25,26,27,28,29,30,40,41,42},{0,1,2,3,4,5,7,8,9,10,11,12,22,23,24,28,29,30,31,32,33,43,44,45},{0,1,2,3,4,5,6,8,9,10,11,12,25,26,27,31,32,33,34,35,36,46,47,48},{0,1,2,3,4,5,6,7,9,10,11,12,28,29,30,34,35,36,37,38,39,49,50,51},{0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,31,32,33,37,38,39,40,41,42},{0,1,2,3,4,5,6,7,8,9,11,12,16,17,18,34,35,36,40,41,42,43,44,45},{0,1,2,3,4,5,6,7,8,9,10,12,19,20,21,37,38,39,43,44,45,46,47,48},{0,1,2,3,4,5,6,7,8,9,10,11,22,23,24,40,41,42,46,47,48,49,50,51},{0,1,3,9},{0,1,3,9},{0,1,3,9},{0,1,2,4,10},{1,2,4,10},{1,2,4,10},{2,3,5,11},{2,3,5,11},{2,3,5,11},{3,4,6,12},{3,4,6,12},{3,4,6,12},{0,4,5,7},{0,4,5,7},{0,4,5,7},{1,5,6,8},{1,5,6,8},{1,5,6,8},{2,6,7,9},{2,6,7,9},{2,6,7,9},{3,7,8,10},{3,7,8,10},{3,7,8,10},{4,8,9,11},{4,8,9,11},{4,8,9,11},{5,9,10,12},{5,9,10,12},{5,9,10,12},{0,6,10,11},{0,6,10,11},{0,6,10,11},{1,7,11,12},{1,7,11,12},{1,7,11,12},{0,2,8,12},{0,2,8,12},{0,2,8,12}]

def witness : SimpleGraph (Fin 52) where
  Adj u v := v ∈ adjacency u
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
instance : DecidableRel witness.Adj := inferInstanceAs
  (DecidableRel fun u v : Fin 52 => v ∈ adjacency u)

lemma two_steps : ∀ u v : Fin 52, u ≠ v →
    witness.Adj u v ∨ ∃ w, witness.Adj u w ∧ witness.Adj w v := by decide
lemma short_walk (u v : Fin 52) : ∃ p : witness.Walk u v, p.length ≤ 2 := by
  by_cases he : u = v
  · subst v; exact ⟨.nil, by simp⟩
  · rcases two_steps u v he with h | ⟨w, huw, hwv⟩
    · exact ⟨.cons h .nil, by simp⟩
    · exact ⟨.cons huw (.cons hwv .nil), by simp⟩
lemma witness_connected : witness.Connected :=
  ⟨fun u v => (short_walk u v).elim fun p _ => p.reachable⟩
lemma square_complete : witness.graphSquare = ⊤ := by
  ext u v
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    obtain ⟨p, hp⟩ := short_walk u v
    exact p.edist_le.trans (by exact_mod_cast hp)

variable {V : Type*} [Fintype V] [DecidableEq V]
def maximumVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  univ.filter fun v => ∀ w, G.degree w ≤ G.degree v

def neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  univ.filter fun v => ∃ u ∈ S, G.Adj v u

noncomputable def squareDegree (G : SimpleGraph V) (v : V) : ℕ := by
  classical
  exact G.graphSquare.degree v

noncomputable def reciprocalSum (G : SimpleGraph V) : ℚ :=
  ∑ v : V, 1 / (squareDegree G v : ℚ)

noncomputable def bound (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  ((neighbors G (maximumVertices G)).card : ℚ) / 2 * ⌊2 * reciprocalSum G⌋₊

def degrees : Fin 52 → ℕ := ![25,24,24,24,24,24,24,24,24,24,24,24,24,4,4,4,5,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4]
lemma degree_eq : ∀ v : Fin 52, witness.degree v = degrees v := by decide
lemma maximum_eq : maximumVertices witness = {0} := by
  unfold maximumVertices
  simp_rw [degree_eq]
  decide
lemma neighborhood_card : (neighbors witness (maximumVertices witness)).card = 25 := by
  rw [maximum_eq]
  decide
lemma square_degree (v : Fin 52) : squareDegree witness v = 51 := by
  classical
  unfold squareDegree
  rw [← card_neighborSet_eq_degree]
  let e : witness.graphSquare.neighborSet v ≃ {w : Fin 52 // w ≠ v} :=
    Equiv.subtypeEquivRight fun w => by rw [square_complete]; simp [ne_comm]
  rw [Fintype.card_congr e]
  simp
lemma reciprocal_sum : reciprocalSum witness = 52 / 51 := by
  unfold reciprocalSum
  simp_rw [square_degree]
  norm_num
lemma bound_eq : bound witness = 25 := by
  have hf : ⌊(104 : ℚ) / 51⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by norm_num)]
    norm_num
  have he : 2 * (52 / 51 : ℚ) = 104 / 51 := by norm_num
  rw [bound, neighborhood_card, reciprocal_sum, he, hf]
  norm_num

def clique : Finset (Fin 52) := univ.filter fun v => v.val < 13
def outer : Finset (Fin 52) := univ \ clique
def forced (c : Fin 52) : Finset (Fin 52) := insert c (outer \ adjacency c)
lemma clique_edges : ∀ c ∈ clique, ∀ w ∈ clique, c ≠ w → witness.Adj c w := by decide
lemma outer_adj : ∀ u ∈ outer, ∀ w : Fin 52, witness.Adj u w → w ∈ clique := by decide
lemma forced_card : ∀ c ∈ clique, 27 ≤ (forced c).card := by decide
lemma outer_card : outer.card = 39 := by decide

/-- A lower bound for EVERY independent dominating set, without powerset enumeration. -/
lemma independent_dominating_lower (D : Finset (Fin 52))
    (hD : witness.IsIndepDominating (D : Set (Fin 52))) : 27 ≤ D.card := by
  classical
  by_cases hc : (D ∩ clique).Nonempty
  · obtain ⟨c, hc⟩ := hc
    have hcd := (mem_inter.mp hc).1
    have hcc := (mem_inter.mp hc).2
    have hs : forced c ⊆ D := by
      intro u hu
      rcases mem_insert.mp hu with rfl | hu
      · exact hcd
      · rcases hD.2 u with hd | ⟨w, hw, huw⟩
        · exact hd
        · have hwc := outer_adj u (mem_sdiff.mp hu).1 w huw
          have he : w = c := by
            by_contra hn
            exact hD.1 hcd hw (Ne.symm hn) (clique_edges c hcc w hwc (Ne.symm hn))
          subst w
          exact False.elim ((mem_sdiff.mp hu).2 huw.symm)
    exact (forced_card c hcc).trans (card_le_card hs)
  · have hs : outer ⊆ D := by
      intro u hu
      rcases hD.2 u with hd | ⟨w, hw, huw⟩
      · exact hd
      · exact False.elim (hc ⟨w, mem_inter.mpr ⟨hw, outer_adj u hu w huw⟩⟩)
    have hh := card_le_card hs
    rw [outer_card] at hh
    omega

def selected : Finset (Fin 52) := forced 0
lemma selected_certificate : witness.IsIndepDominating (selected : Set (Fin 52)) ∧
    selected.card = 27 := by
  constructor
  · change (∀ u ∈ selected, ∀ v ∈ selected, u ≠ v → ¬ witness.Adj u v) ∧
      (∀ v, v ∈ selected ∨ ∃ w ∈ selected, witness.Adj v w)
    decide
  · decide
lemma independent_domination_eq : witness.indepDominationNumber = 27 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨selected, selected_certificate.1.1, selected_certificate.1.2,
      selected_certificate.2⟩
  · apply le_csInf
    · exact ⟨27, selected, selected_certificate.1.1, selected_certificate.1.2,
        selected_certificate.2⟩
    · rintro n ⟨D, hD⟩
      rw [← hD.card_eq]
      exact independent_dominating_lower D ⟨hD.isIndep, hD.isDominating⟩

theorem conjecture433_upper_M : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected → 3 < Fintype.card W →
      (G.indepDominationNumber : ℚ) ≤ bound G := by
  intro h
  have hb := h (Fin 52) witness witness_connected (by decide)
  rw [bound_eq, independent_domination_eq] at hb
  norm_num at hb

#print axioms conjecture433_upper_M
#print axioms square_complete
#print axioms independent_domination_eq
end WOWII433Proof
