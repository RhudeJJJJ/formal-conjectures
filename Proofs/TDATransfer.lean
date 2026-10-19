import Proofs.TDAOptimal

/-! Exact budget transfer after deleting an edge incident with a degree-at-least-three vertex. -/

namespace TotalDominationAnnihilationProof
open Finset

variable {V : Type*} [DecidableEq V]

/-- Restoring an edge changes two actual entries. If both were selected, one
high-degree endpoint is replaced by a missing low-degree vertex. -/
theorem budget_transfer_edge (d d' : V → ℕ) (m : ℕ) (hm : 0 < m)
    (u v : V) (hdelta : ∀ x, d x = d' x + (if x = u then 1 else 0) +
      (if x = v then 1 else 0)) (hvhigh : 3 ≤ d v)
    (L A : Finset V) (hL : ∀ x ∈ L, d x ≤ 2) (hlarge : m < ∑ x ∈ L, d x)
    (hA : ∑ x ∈ A, d' x ≤ m - 1) :
    ∃ B : Finset V, B.card = A.card ∧ ∑ x ∈ B, d x ≤ m := by
  classical
  have hsum : (∑ x ∈ A, d x) = (∑ x ∈ A, d' x) +
      (if u ∈ A then 1 else 0) + (if v ∈ A then 1 else 0) := by
    rw [sum_congr rfl (fun x _ => hdelta x)]
    simp [sum_add_distrib]
  by_cases hfit : ∑ x ∈ A, d x ≤ m
  · exact ⟨A, rfl, hfit⟩
  · have hvA : v ∈ A := by
      by_contra hvA
      simp only [if_neg hvA] at hsum
      split_ifs at hsum <;> omega
    have hupper : ∑ x ∈ A, d x ≤ m + 1 := by
      split_ifs at hsum <;> omega
    have hvL : v ∉ L := by
      intro hvL
      have hl := hL v hvL
      omega
    have hex : ∃ w ∈ L, w ∉ A := by
      by_contra hbad
      have hLA : L ⊆ A := by
        intro w hw
        by_contra hwA
        exact hbad ⟨w, hw, hwA⟩
      have hsub : insert v L ⊆ A := insert_subset hvA hLA
      have hle : (∑ x ∈ insert v L, d x) ≤ ∑ x ∈ A, d x :=
        sum_le_sum_of_subset_of_nonneg hsub (by intros; omega)
      rw [sum_insert hvL] at hle
      omega
    obtain ⟨w, hwL, hwA⟩ := hex
    have hwE : w ∉ A.erase v := fun hw => hwA (mem_of_mem_erase hw)
    have hcard : (insert w (A.erase v)).card = A.card := by
      rw [card_insert_of_notMem hwE, card_erase_of_mem hvA]
      have hp := card_pos.mpr ⟨v, hvA⟩
      omega
    have herase := sum_erase_add A d hvA
    have hwlow := hL w hwL
    refine ⟨insert w (A.erase v), hcard, ?_⟩
    rw [sum_insert hwE]
    omega

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.budget_transfer_edge
