/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Domination
import Proofs.WOWIIModalDefinitions
import Mathlib.Tactic

/-! WOWII 252, Gebendorfer's explicit 30-vertex graph, 8 September 2026.
OpenAI Codex assisted with formalization. -/
namespace WOWII252Proof
open SimpleGraph Finset WOWIIModal
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def adjacency : Fin 30 → Finset (Fin 30) := ![{1,6,7,8,9,18,19},{0,10,11,12,13,20,21},{3,6,10,14,15,22,23},{2,7,11,16,17,24,25},{5,8,12,14,16,26,27},{4,9,13,15,17,28,29},{0,2,14,18,28},{0,3},{0,4,16},{0,5},{1,2,12,23,29},{1,3,16,28},{1,4,10,27},{1,5,15,21,25},{2,4,6},{2,5,13,22},{3,4,8,11},{3,5},{0,6,25,27,29},{0},{1},{1,13},{2,15,27},{2,10},{3},{3,13,18,27},{4},{4,12,18,22,25},{5,6,11},{5,10,18}]

def witness : SimpleGraph (Fin 30) where
  Adj u v := v ∈ adjacency u
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
instance : DecidableRel witness.Adj := inferInstanceAs
  (DecidableRel fun u v : Fin 30 => v ∈ adjacency u)

def parent : Fin 30 → Fin 30 := ![0,0,6,7,8,9,0,0,0,0,1,1,1,1,6,13,8,3,0,0,1,1,2,10,3,18,4,18,6,18]
def depth : Fin 30 → ℕ := ![0,1,2,2,2,2,1,1,1,1,2,2,2,2,2,3,2,3,1,1,2,2,3,3,3,2,3,2,2,2]
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

def degrees : Fin 30 → ℕ := ![7,7,7,7,7,7,5,2,3,2,5,4,4,5,3,4,4,2,5,1,1,2,3,2,1,4,1,5,3,3]
lemma degree_eq : ∀ v : Fin 30, witness.degree v = degrees v := by decide
lemma candidates_eq : modalCandidates witness = {7} := by
  unfold modalCandidates frequency
  simp_rw [degree_eq]
  decide
lemma mode_eq : modeMin witness = 7 := by rw [modeMin, candidates_eq]; simp

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

def packing : Fin 6 → Fin 30 := ![19,20,24,26,23,28]
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

theorem conjecture252 : ¬ ∀ (W : Type) [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj], G.Connected → (∀ v, ∃ w, G.Adj v w) → C4Free G →
      modeMin G ≤ G.totalDominationNumber := by
  intro h
  have hb := h (Fin 30) witness witness_connected witness_no_isolates witness_C4Free
  rw [mode_eq, total_eq] at hb
  omega

#print axioms conjecture252
#print axioms witness_C4Free
#print axioms total_eq
end WOWII252Proof
