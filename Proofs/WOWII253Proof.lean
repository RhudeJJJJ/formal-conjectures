/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Proofs.WOWIIModalDefinitions
import Mathlib.Tactic

/-! WOWII 253, Gebendorfer's explicit 30-vertex graph, undated supplied manuscript.
OpenAI Codex assisted with formalization. -/
namespace WOWII253Proof
open SimpleGraph Finset WOWIIModal
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def adjacency : Fin 30 → Finset (Fin 30) := ![{1,6,8,12,13,14},{0,9,11,15,16,17},{3,6,7,18,19,20},{2,9,10,21,22,23},{5,7,8,24,25,26},{4,10,11,27,28,29},{0,2,26},{2,4,13},{0,4,18,22},{1,3},{3,5},{1,5},{0},{0,7,21,29},{0,20,27},{1,18,23,26,29},{1,20,21},{1,27},{2,8,15,27},{2},{2,14,16,29},{3,13,16,26,27},{3,8,29},{3,15},{4},{4},{4,6,15,21},{5,14,17,18,21},{5},{5,13,15,20,22}]

def witness : SimpleGraph (Fin 30) where
  Adj u v := v ∈ adjacency u
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
instance : DecidableRel witness.Adj := inferInstanceAs
  (DecidableRel fun u v : Fin 30 => v ∈ adjacency u)

def parent : Fin 30 → Fin 30 := ![0,0,6,9,8,11,0,13,0,1,3,1,0,0,0,1,1,1,8,2,14,13,8,15,4,4,6,14,5,13]
def depth : Fin 30 → ℕ := ![0,1,2,3,2,3,1,2,1,2,4,2,1,1,1,2,2,2,2,3,2,2,2,3,3,3,2,2,4,2]
lemma parent_step : ∀ v : Fin 30, v ≠ 0 →
    witness.Adj v (parent v) ∧ depth (parent v) < depth v := by decide
lemma root_reachable (v : Fin 30) : witness.Reachable v 0 := by
  have aux : ∀ n : ℕ, ∀ w : Fin 30, depth w = n → witness.Reachable w 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      by_cases he : w = 0
      · subst w; exact .refl _
      · have hs := parent_step w he
        exact hs.1.reachable.trans (ih (depth (parent w)) (by omega) (parent w) rfl)
  exact aux _ v rfl
lemma witness_connected : witness.Connected :=
  ⟨fun u v => (root_reachable u).trans (root_reachable v).symm⟩

def degrees : Fin 30 → ℕ := ![6,6,6,6,6,6,3,3,4,2,2,2,1,4,3,5,3,2,4,1,4,5,3,2,1,1,4,5,1,5]
lemma degree_eq : ∀ v : Fin 30, witness.degree v = degrees v := by decide
lemma candidates_eq : modalCandidates witness = {6} := by
  unfold modalCandidates frequency
  simp_rw [degree_eq]
  decide
lemma mode_eq : modeMin witness = 6 := by rw [modeMin, candidates_eq]; simp

lemma common_bound : ∀ a c : Fin 30, a ≠ c →
    (adjacency a ∩ adjacency c).card ≤ 1 := by decide
lemma witness_C4Free : C4Free witness := by
  intro a b c d hac hbd hab hbc hcd hda
  apply hbd
  apply card_le_one.mp (common_bound a c hac)
  · exact mem_inter.mpr ⟨hab, hbc.symm⟩
  · exact mem_inter.mpr ⟨hda.symm, hcd⟩

def selected : Finset (Fin 30) := {0,1,2,3,4,5}
lemma selected_total : witness.IsTotalDominating (selected : Set (Fin 30)) := by
  change ∀ v : Fin 30, ∃ w ∈ selected, witness.Adj v w
  decide
lemma witness_no_isolates (v : Fin 30) : ∃ w, witness.Adj v w := by
  obtain ⟨w, _, hw⟩ := selected_total v
  exact ⟨w, hw⟩
lemma total_upper : witness.totalDominationNumber ≤ 6 :=
  Nat.sInf_le ⟨selected, selected_total, by decide⟩

def packing : Fin 6 → Fin 30 := ![12,19,24,28,16,23]
lemma packing_disjoint : ∀ i j : Fin 6, ∀ w : Fin 30,
    witness.Adj (packing i) w → witness.Adj (packing j) w → i = j := by decide
lemma selected_lower (D : Finset (Fin 30))
    (hD : witness.IsTotalDominating (D : Set (Fin 30))) : 6 ≤ D.card := by
  classical
  choose f hfm hfa using fun i : Fin 6 => hD (packing i)
  let g : Fin 6 → D := fun i => ⟨f i, hfm i⟩
  have hi : Function.Injective g := by
    intro i j he
    have hf : f i = f j := congrArg Subtype.val he
    exact packing_disjoint i j (f i) (hfa i) (hf ▸ hfa j)
  simpa using Fintype.card_le_of_injective g hi
lemma total_eq : witness.totalDominationNumber = 6 := by
  apply le_antisymm total_upper
  apply le_csInf
  · exact ⟨6, selected, selected_total, by decide⟩
  · rintro n ⟨D, hD⟩
    rw [← hD.card_eq]
    exact selected_lower D hD.isTotalDominating

lemma no_triangle : ∀ a b : Fin 30, witness.Adj a b →
    adjacency a ∩ adjacency b = ∅ := by decide

lemma witness_girth_lower : (5 : ℕ∞) ≤ witness.egirth := by
  apply le_egirth.mpr
  intro a w hw
  suffices 5 ≤ w.length by exact_mod_cast this
  have hlen := hw.three_le_length
  by_contra hn
  have hshort : w.length = 3 ∨ w.length = 4 := by omega
  rcases hshort with he | he
  · have h01 := w.adj_getVert_succ (i := 0) (by omega)
    have h12 := w.adj_getVert_succ (i := 1) (by omega)
    have h20 := w.adj_getVert_succ (i := 2) (by omega)
    have hend : w.getVert 3 = w.getVert 0 := by
      rw [← he, Walk.getVert_length, Walk.getVert_zero]
    have hi : w.getVert 2 ∈ adjacency (w.getVert 0) ∩ adjacency (w.getVert 1) := by
      refine mem_inter.mpr ⟨?_, ?_⟩
      · change witness.Adj (w.getVert 0) (w.getVert 2)
        simpa only [Nat.reduceAdd, hend] using h20.symm
      · exact h12
    rw [no_triangle _ _ h01] at hi
    exact notMem_empty _ hi
  · exact no_four_cycle witness witness_C4Free w hw he

def fiveCycle : witness.Walk 0 0 :=
  .cons (show witness.Adj 0 8 by decide)
    (.cons (show witness.Adj 8 18 by decide)
      (.cons (show witness.Adj 18 15 by decide)
        (.cons (show witness.Adj 15 1 by decide)
          (.cons (show witness.Adj 1 0 by decide) .nil))))
lemma fiveCycle_isCycle : fiveCycle.IsCycle := by
  rw [Walk.isCycle_def, Walk.isTrail_def]
  decide
lemma witness_egirth_eq : witness.egirth = 5 := by
  apply le_antisymm _ witness_girth_lower
  have h := egirth_le_length fiveCycle_isCycle
  simpa [fiveCycle] using h

theorem conjecture253 : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected → (∀ v, ∃ w, G.Adj v w) → (5 : ℕ∞) ≤ G.egirth →
      1 + modeMin G ≤ G.totalDominationNumber := by
  intro h
  have hb := h (Fin 30) witness witness_connected witness_no_isolates witness_girth_lower
  rw [mode_eq, total_eq] at hb
  omega

#print axioms conjecture253
#print axioms witness_egirth_eq
#print axioms total_eq
end WOWII253Proof
