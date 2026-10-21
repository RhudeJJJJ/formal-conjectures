import Mathlib

namespace OeisA381054

/-- The largest positive divisor not exceeding the integer square root. -/
def smallDivisor (q : ℕ) : ℕ :=
  ((Finset.range (Nat.sqrt q + 1)).filter fun d => 0 < d ∧ d ∣ q).sup id

/-- Difference of the integer square roots of the closest factor pair. -/
def gap (q : ℕ) : ℤ :=
  (Nat.sqrt (q / smallDivisor q) : ℤ) - (Nat.sqrt (smallDivisor q) : ℤ)

/-- Admissible positive multipliers in the general family. -/
def Admissible (m n k : ℕ) : Prop := 0 < k ∧ gap (n * k) = (m : ℤ)

instance (m n k : ℕ) : Decidable (Admissible m n k) :=
  inferInstanceAs (Decidable (0 < k ∧ gap (n * k) = (m : ℤ)))

/-- Least positive admissible multiplier, with value zero if none exists. -/
noncomputable def aFamily (m n : ℕ) : ℕ := sInf {k | Admissible m n k}

private theorem a_family_eq (m n k : ℕ) (hk : Admissible m n k)
    (hsmall : ∀ j ∈ Finset.range k, ¬ Admissible m n j) : aFamily m n = k := by
  apply IsLeast.csInf_eq
  refine ⟨hk, ?_⟩
  intro j hj
  by_contra! h
  exact hsmall j (Finset.mem_range.mpr h) hj

/-- The sequence A381054 itself is the member with gap one. -/
noncomputable def a (n : ℕ) : ℕ := aFamily 1 n

theorem a_1 : a 1 = 5 := a_family_eq 1 1 5 (by decide) (by decide)
theorem a_2 : a 2 = 4 := a_family_eq 1 2 4 (by decide) (by decide)
theorem a_3 : a 3 = 4 := a_family_eq 1 3 4 (by decide) (by decide)
theorem a_4 : a 4 = 2 := a_family_eq 1 4 2 (by decide) (by decide)
theorem a_5 : a 5 = 1 := a_family_eq 1 5 1 (by decide) (by decide)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem a_family_3_11 : aFamily 3 11 = 37 :=
  a_family_eq 3 11 37 (by decide) (by decide)

/-- The general-family comment, restricted to inputs where the minimum exists.
The square uses integer subtraction, including when the proposed value is zero. -/
def FamilyConjecture : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → (∃ k, Admissible m n k) →
    ((aFamily m n : ℤ) = ((Nat.sqrt n : ℤ) - (m : ℤ)) ^ 2 ↔
      n.Prime ∧ m ^ 2 + 1 < n)

theorem not_family_conjecture : ¬ FamilyConjecture := by
  intro h
  have heq := (h 3 11 (by decide) (by decide) ⟨37, by decide⟩).mpr (by decide)
  rw [a_family_3_11] at heq
  norm_num [show Nat.sqrt 11 = 3 from by decide] at heq

end OeisA381054

#print axioms OeisA381054.a_family_3_11
#print axioms OeisA381054.not_family_conjecture
