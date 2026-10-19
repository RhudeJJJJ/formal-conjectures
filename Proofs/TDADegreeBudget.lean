import Proofs.TDAOptimal

/-! Integer degree-budget rounding, using cheapest subsets and no sorted-prefix equivalence. -/

namespace TotalDominationAnnihilationProof
open Finset

variable {V : Type*} [DecidableEq V]

open scoped Classical in
/-- If all low-degree entries fit, the entries of size at least three supply
the remaining cardinality by the smallest-high-degrees argument. -/
theorem exists_rounded_budget (S L : Finset V) (d : V → ℕ) (m : ℕ)
    (hLS : L ⊆ S) (hhand : ∑ v ∈ S, d v = 2 * m)
    (hbudget : ∑ v ∈ L, d v ≤ m) (hhigh : ∀ v ∈ S \ L, 3 ≤ d v) :
    ∃ A : Finset V, A ⊆ S ∧ (∑ v ∈ A, d v ≤ m) ∧
      6 * L.card + 3 * (S \ L).card ≤ 6 * A.card + (∑ v ∈ L, d v) + 5 := by
  let H := S \ L
  let r := H.card
  let B := ∑ v ∈ L, d v
  let E := ∑ v ∈ H, d v
  have hsum : E + B = 2 * m := by
    have hs := sum_sdiff hLS (f := d)
    omega
  have hE : 3 * r ≤ E := by
    calc
      _ = ∑ _v ∈ H, (3 : ℕ) := by simp [r, Nat.mul_comm]
      _ ≤ _ := sum_le_sum hhigh
  by_cases hsmall : 3 * r ≤ B + 5
  · exact ⟨L, hLS, hbudget, by change 6 * L.card + 3 * r ≤ 6 * L.card + B + 5; omega⟩
  · let t := (3 * r - B) / 6
    have hr : 0 < r := by omega
    have ht : t ≤ H.card := by dsimp [t, r]; omega
    obtain ⟨T, hTH, hTc, hTsum⟩ := exists_subset_average H d t ht
    have htbound : 6 * t + B ≤ 3 * r := by dsimp [t]; omega
    have htround : 3 * r ≤ 6 * t + B + 5 := by dsimp [t]; omega
    have hTB : (∑ v ∈ T, d v) + B ≤ m := by
      have hmul := Nat.mul_le_mul_left E htbound
      have hmul' := Nat.mul_le_mul_right B hE
      change r * (∑ v ∈ T, d v) ≤ t * E at hTsum
      nlinarith
    have hdis : Disjoint L T := by
      apply disjoint_left.mpr
      intro v hvL hvT
      exact (mem_sdiff.mp (hTH hvT)).2 hvL
    have hAS : L ∪ T ⊆ S := union_subset hLS (subset_trans hTH sdiff_subset)
    refine ⟨L ∪ T, hAS, ?_, ?_⟩
    · rw [sum_union hdis]
      change (∑ v ∈ L, d v) + (∑ v ∈ T, d v) ≤ m
      omega
    · rw [card_union_of_disjoint hdis, hTc]
      change 6 * L.card + 3 * r ≤ 6 * (L.card + t) + B + 5
      omega

end TotalDominationAnnihilationProof

#print axioms TotalDominationAnnihilationProof.exists_rounded_budget
