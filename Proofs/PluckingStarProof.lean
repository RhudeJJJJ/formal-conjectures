/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Mathlib.Tactic

namespace PluckingStarProof
set_option maxHeartbeats 0
open Finset

abbrev Sequence := ℤ → ℤ

def Nonnegative (a : Sequence) : Prop := ∀ j, 0 ≤ a j
def Supported (a : Sequence) (N : ℕ) : Prop := ∀ j, j < 0 ∨ (N : ℤ) < j → a j = 0
def Unimodal (a : Sequence) : Prop :=
  ∃ t : ℤ, (∀ i j, i ≤ j → j ≤ t → a i ≤ a j) ∧
    (∀ i j, t ≤ i → i ≤ j → a j ≤ a i)
def NoReversal (a : Sequence) : Prop :=
  ∀ i j : ℤ, i < j → a (i+1) < a i → a (j+1) ≤ a j

/-- Multiplication of a coefficient sequence by 1+q+...+q^(h-1). -/
def uniform (a : Sequence) (h : ℕ) (j : ℤ) : ℤ :=
  ∑ k ∈ range h, a (j - (k : ℤ))

theorem uniform_succ (a : Sequence) (h : ℕ) (j : ℤ) :
    uniform a (h+1) j = uniform a h j + a (j-h) := by
  simp [uniform, sum_range_succ]

theorem uniform_diff (a : Sequence) (h : ℕ) (j : ℤ) :
    uniform a h (j+1) - uniform a h j = a (j+1) - a (j+1-h) := by
  induction h with
  | zero => simp [uniform]
  | succ h ih =>
    rw [uniform_succ, uniform_succ]
    have he : j+1-((h+1 : ℕ) : ℤ) = j-(h : ℤ) := by push_cast; ring
    rw [he]
    linarith

theorem uniform_nonnegative {a : Sequence} (ha : Nonnegative a) (h : ℕ) :
    Nonnegative (uniform a h) := by
  intro j
  exact sum_nonneg fun _ _ => ha _

theorem uniform_supported {a : Sequence} {N : ℕ} (ha : Supported a N) (h : ℕ) :
    Supported (uniform a h) (N+h) := by
  intro j hj
  apply sum_eq_zero
  intro k hk
  apply ha
  have hk' := mem_range.mp hk
  rcases hj with hj | hj
  · left; omega
  · right; push_cast at hj; omega

theorem monotone_between {a : Sequence} {i j : ℤ} (hij : i ≤ j)
    (hs : ∀ k : ℤ, i ≤ k → k < j → a k ≤ a (k+1)) : a i ≤ a j := by
  induction j, hij using Int.leInduction with
  | base => rfl
  | succ j hij ih =>
    exact le_trans (ih fun k hk hj => hs k hk (by omega)) (hs j hij (by omega))

theorem antitone_between {a : Sequence} {i j : ℤ} (hij : i ≤ j)
    (hs : ∀ k : ℤ, i ≤ k → k < j → a (k+1) ≤ a k) : a j ≤ a i := by
  have h := monotone_between (a := fun k => -a k) hij
    (fun k hk hj => neg_le_neg (hs k hk hj))
  linarith

/-- Finite support turns the absence of a descent followed by an ascent into an actual peak. -/
theorem unimodal_of_noReversal {a : Sequence} {N : ℕ}
    (hn : Nonnegative a) (hs : Supported a N) (hr : NoReversal a) : Unimodal a := by
  classical
  by_cases hex : ∃ n : ℕ, a ((n : ℤ)+1) < a n
  · let n := Nat.find hex
    have hd : a ((n : ℤ)+1) < a n := Nat.find_spec hex
    refine ⟨n, ?_, ?_⟩
    · intro i j hij hj
      apply monotone_between hij
      intro k _ hkj
      by_cases hk : k < 0
      · rw [hs k (Or.inl hk)]; exact hn _
      · have hkn : k.toNat < n := by omega
        have hh := Nat.find_min hex hkn
        have he : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
        rw [he] at hh
        exact le_of_not_gt hh
    · intro i j hi hij
      apply antitone_between hij
      intro k hik _
      by_cases hk : k = (n : ℤ)
      · simpa [hk] using le_of_lt hd
      · exact hr n k (by omega) hd
  · have hm : Monotone a := monotone_int_of_le_succ fun k => by
      by_cases hk : k < 0
      · rw [hs k (Or.inl hk)]; exact hn _
      · have hh : ¬ a ((k.toNat : ℤ)+1) < a k.toNat := by
          intro h; exact hex ⟨k.toNat,h⟩
        simpa [Int.toNat_of_nonneg (show 0 ≤ k by omega)] using le_of_not_gt hh
    have hz : ∀ k : ℤ, a k = 0 := by
      intro k
      by_cases hk : (N : ℤ)+1 ≤ k
      · exact hs k (Or.inr (by omega))
      · have hh := hm (show k ≤ (N : ℤ)+1 by omega)
        rw [hs ((N : ℤ)+1) (Or.inr (by omega))] at hh
        exact le_antisymm hh (hn k)
    refine ⟨0, ?_, ?_⟩ <;> intros <;> simp only [hz, le_refl]

/-- A uniform window preserves unimodality without a symmetry hypothesis. -/
theorem uniform_noReversal {a : Sequence} (hu : Unimodal a) {h : ℕ} (hh : 0 < h) :
    NoReversal (uniform a h) := by
  obtain ⟨t,hl,hr⟩ := hu
  intro i j hij hd
  have hdi : a (i+1) < a (i+1-h) := by
    have he := uniform_diff a h i
    linarith
  have hit : t < i+1 := by
    by_contra hnot
    have he := hl (i+1-h) (i+1) (by omega) (by omega)
    omega
  by_cases hjt : t ≤ j+1-h
  · have he := hr (j+1-h) (j+1) hjt (by omega)
    have hdj := uniform_diff a h j
    linarith
  · have hit' : i+1-h ≤ t := by omega
    have hleft := hl (i+1-h) (j+1-h) (by omega) (by omega)
    have hright := hr (i+1) (j+1) (by omega) (by omega)
    have hdj := uniform_diff a h j
    linarith

theorem uniform_unimodal {a : Sequence} {N : ℕ} (hn : Nonnegative a)
    (hs : Supported a N) (hu : Unimodal a) {h : ℕ} (hh : 0 < h) :
    Unimodal (uniform a h) :=
  unimodal_of_noReversal (uniform_nonnegative hn h) (uniform_supported hs h)
    (uniform_noReversal hu hh)

/-- The first window already smooths every nonnegative sequence supported in [0,m]. -/
theorem first_window {a : Sequence} {m : ℕ} (_hm : 0 < m)
    (hn : Nonnegative a) (hs : Supported a m) : Unimodal (uniform a m) := by
  apply unimodal_of_noReversal (uniform_nonnegative hn m) (uniform_supported hs m)
  intro i j hij hd
  have hi : (m : ℤ)-1 ≤ i := by
    by_contra h
    have he := uniform_diff a m i
    rw [hs (i+1-m) (Or.inl (by omega))] at he
    have ha := hn (i+1)
    omega
  have hj : (m : ℤ) < j+1 := by omega
  have he := uniform_diff a m j
  rw [hs (j+1) (Or.inr hj)] at he
  have ha := hn (j+1-m)
  omega

/-- Successively multiply by [m]_q,[m-1]_q,...,[1]_q. -/
def factors (a : Sequence) : ℕ → Sequence
  | 0 => a
  | m+1 => factors (uniform a (m+1)) m

theorem factors_shape (m : ℕ) {a : Sequence} {N : ℕ}
    (hn : Nonnegative a) (hs : Supported a N) (hu : Unimodal a) :
    Nonnegative (factors a m) ∧ ∃ M, Supported (factors a m) M ∧ Unimodal (factors a m) := by
  induction m generalizing a N with
  | zero => exact ⟨hn,N,hs,hu⟩
  | succ m ih =>
    exact ih (uniform_nonnegative hn _) (uniform_supported hs _)
      (uniform_unimodal hn hs hu (by omega))

theorem weighted_factorial {a : Sequence} {m : ℕ} (hm : 0 < m)
    (hn : Nonnegative a) (hs : Supported a m) :
    Unimodal (factors a m) := by
  cases m with
  | zero => omega
  | succ m =>
    exact (factors_shape m (uniform_nonnegative hn _) (uniform_supported hs _)
      (first_window (by omega) hn hs)).2.choose_spec.2

theorem uniform_comm (a : Sequence) (h k : ℕ) :
    uniform (uniform a h) k = uniform (uniform a k) h := by
  funext j
  simp only [uniform]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro l _
  congr 1
  ring

theorem factors_uniform (a : Sequence) (h m : ℕ) :
    factors (uniform a h) m = uniform (factors a m) h := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    change factors (uniform (uniform a h) (m+1)) m =
      uniform (factors (uniform a (m+1)) m) h
    rw [uniform_comm]
    exact ih _

theorem factors_shift (a : Sequence) (r : ℤ) (m : ℕ) :
    factors (fun j => a (j-r)) m = fun j => factors a m (j-r) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    have he : uniform (fun j => a (j-r)) (m+1) = fun j => uniform a (m+1) (j-r) := by
      funext j
      apply sum_congr rfl
      intro k _
      exact congrArg a (show (j-(k : ℤ))-r = (j-r)-(k : ℤ) by ring)
    change factors (uniform (fun j => a (j-r)) (m+1)) m = _
    rw [he,ih]
    rfl

theorem factors_sum {I : Type*} (s : Finset I) (a : I → Sequence) (m : ℕ) :
    factors (fun j => ∑ i ∈ s, a i j) m = fun j => ∑ i ∈ s, factors (a i) m j := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    have he : uniform (fun j => ∑ i ∈ s, a i j) (m+1) =
        fun j => ∑ i ∈ s, uniform (a i) (m+1) j := by
      funext j
      exact sum_comm
    change factors (uniform (fun j => ∑ i ∈ s, a i j) (m+1)) m = _
    rw [he,ih]
    rfl

theorem factors_zero (m : ℕ) : factors (fun _ => 0) m = fun _ => 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have he : uniform (fun _ => 0) (m+1) = fun _ => 0 := by funext j; simp [uniform]
    change factors (uniform (fun _ => 0) (m+1)) m = _
    rw [he,ih]

def oneSeq (j : ℤ) : ℤ := if j = 0 then 1 else 0
def qFactorial (m : ℕ) : Sequence := factors oneSeq m

theorem qFactorial_succ (m : ℕ) :
    qFactorial (m+1) = uniform (qFactorial m) (m+1) := by
  exact factors_uniform oneSeq (m+1) m

/-- Fin n indexes the star leaves from right to left. -/
def eligibility {n : ℕ} (f : Fin n → ℕ) (j : ℤ) : ℤ :=
  ∑ i : Fin n, if f i = 1 then oneSeq (j-i.val) else 0

/-- The delayed leaf-removal recurrence, defined before any factorization. -/
def pluck : (n : ℕ) → (Fin n → ℕ) → Sequence
  | 0, _ => oneSeq
  | n+1, f => fun j => ∑ i : Fin (n+1), if f i = 1 then
      pluck n (fun k => max 1 (f (i.succAbove k)-1)) (j-i.val) else 0

theorem pluck_all_one (n : ℕ) : pluck n (fun _ => 1) = qFactorial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext j
    change (∑ i : Fin (n+1), if (1 : ℕ) = 1 then
      pluck n (fun k => max 1 ((1 : ℕ)-1)) (j-i.val) else 0) = _
    simp only [Nat.sub_self, max_eq_left (show 0 ≤ (1 : ℕ) by omega),ih]
    rw [qFactorial_succ]
    exact Fin.sum_univ_eq_sum_range (fun i => qFactorial n (j-(i : ℤ))) (n+1)

theorem factors_eligibility {n : ℕ} (f : Fin n → ℕ) (m : ℕ) (j : ℤ) :
    factors (eligibility f) m j =
      ∑ i : Fin n, if f i = 1 then qFactorial m (j-i.val) else 0 := by
  unfold eligibility
  rw [factors_sum]
  apply sum_congr rfl
  intro i _
  by_cases hi : f i = 1
  · simp only [hi, ↓reduceIte]
    exact congrFun (factors_shift oneSeq (i.val : ℤ) m) j
  · simp only [hi, ↓reduceIte,factors_zero]

theorem pluck_factorization {n : ℕ} {f : Fin (n+1) → ℕ}
    (hf : ∀ i, f i = 1 ∨ f i = 2) : pluck (n+1) f = factors (eligibility f) n := by
  funext j
  change (∑ i : Fin (n+1), if f i = 1 then
    pluck n (fun k => max 1 (f (i.succAbove k)-1)) (j-i.val) else 0) = _
  have he : ∀ i : Fin (n+1), (fun k => max 1 (f (i.succAbove k)-1)) = fun _ => 1 := by
    intro i
    funext k
    rcases hf (i.succAbove k) with h | h <;> simp [h]
  simp_rw [he,pluck_all_one]
  exact (factors_eligibility f n j).symm

theorem eligibility_nonnegative {n : ℕ} (f : Fin n → ℕ) : Nonnegative (eligibility f) := by
  intro j
  apply sum_nonneg
  intro i _
  exact ite_nonneg (by unfold oneSeq; split_ifs <;> omega) (by omega)

theorem eligibility_supported {n : ℕ} (f : Fin (n+1) → ℕ) :
    Supported (eligibility f) n := by
  intro j hj
  apply sum_eq_zero
  intro i _
  have hi := i.isLt
  simp only [oneSeq]
  split_ifs <;> omega

def UnimodalCoefficients (a : Sequence) : Prop :=
  ∃ t : ℕ, (∀ i j : ℕ, i ≤ j → j ≤ t → a i ≤ a j) ∧
    (∀ i j : ℕ, t ≤ i → i ≤ j → a j ≤ a i)

theorem natural_peak {a : Sequence} (ha : Unimodal a) : UnimodalCoefficients a := by
  obtain ⟨t,hl,hr⟩ := ha
  refine ⟨t.toNat, ?_, ?_⟩
  · intro i j hij hj
    by_cases ht : 0 ≤ t
    · exact hl i j (by omega) (by omega)
    · have hz : t.toNat = 0 := Int.toNat_of_nonpos (by omega)
      have hij' : i = j := by omega
      simp [hij']
  · intro i j hi hij
    exact hr i j (by omega) (by omega)

theorem zero_support_unimodal {a : Sequence} (hn : Nonnegative a) (hs : Supported a 0) :
    Unimodal a := by
  have hu := first_window (m := 1) (by omega) hn
    (show Supported a 1 from fun j hj => hs j (by omega))
  have he : uniform a 1 = a := by funext j; simp [uniform]
  rw [he] at hu
  exact hu

/-- Conjecture 4.1, for every finite ordered star and every binary delay arrangement. -/
theorem sequence_unimodal : ∀ n : ℕ, ∀ f : Fin n → ℕ, (∀ i, f i = 1 ∨ f i = 2) →
    UnimodalCoefficients (pluck n f) := by
  intro n f hf
  cases n with
  | zero =>
    apply natural_peak
    apply zero_support_unimodal
    · intro j; change 0 ≤ oneSeq j; unfold oneSeq; split_ifs <;> omega
    · intro j hj
      change oneSeq j = 0
      simp only [oneSeq]
      split_ifs <;> omega
  | succ n =>
    rw [pluck_factorization hf]
    apply natural_peak
    cases n with
    | zero => exact zero_support_unimodal (eligibility_nonnegative f) (eligibility_supported f)
    | succ n =>
      exact weighted_factorial (by omega) (eligibility_nonnegative f) (eligibility_supported f)

/-- The same operational recurrence as an actual formal polynomial. -/
noncomputable def pluckPolynomial : (n : ℕ) → (Fin n → ℕ) → Polynomial ℤ
  | 0, _ => 1
  | n+1, f => ∑ i : Fin (n+1), if f i = 1 then
      Polynomial.X ^ i.val * pluckPolynomial n (fun k => max 1 (f (i.succAbove k)-1)) else 0

theorem pluck_negative (n : ℕ) (f : Fin n → ℕ) (j : ℤ) (hj : j < 0) :
    pluck n f j = 0 := by
  induction n generalizing j with
  | zero => simp [pluck,oneSeq,show j ≠ 0 by omega]
  | succ n ih =>
    change (∑ i : Fin (n+1), if f i = 1 then _ else 0) = 0
    apply sum_eq_zero
    intro i _
    split_ifs
    · exact ih _ _ (by omega)
    · rfl

theorem pluck_nonnegative (n : ℕ) (f : Fin n → ℕ) : Nonnegative (pluck n f) := by
  induction n with
  | zero => intro j; change 0 ≤ oneSeq j; unfold oneSeq; split_ifs <;> omega
  | succ n ih =>
    intro j
    apply sum_nonneg
    intro i _
    exact ite_nonneg (ih _ _) (by omega)

theorem polynomial_coeff (n : ℕ) (f : Fin n → ℕ) (j : ℕ) :
    (pluckPolynomial n f).coeff j = pluck n f j := by
  induction n generalizing j with
  | zero => simp [pluckPolynomial,pluck,oneSeq,Polynomial.coeff_one]
  | succ n ih =>
    change (∑ i : Fin (n+1), if f i = 1 then
      Polynomial.X ^ i.val * pluckPolynomial n (fun k => max 1 (f (i.succAbove k)-1)) else 0).coeff j = _
    rw [Polynomial.finsetSum_coeff]
    change (∑ i : Fin (n+1), _) = ∑ i : Fin (n+1), _
    apply sum_congr rfl
    intro i _
    split_ifs with hi
    · rw [Polynomial.coeff_X_pow_mul']
      by_cases hj : i.val ≤ j
      · rw [if_pos hj,ih]
        congr 1
        omega
      · rw [if_neg hj]
        exact (pluck_negative _ _ _ (by omega)).symm
    · simp

theorem polynomial_nonnegative (n : ℕ) (f : Fin n → ℕ) (j : ℕ) :
    0 ≤ (pluckPolynomial n f).coeff j := by
  rw [polynomial_coeff]
  exact pluck_nonnegative n f j

def PolynomialUnimodal (p : Polynomial ℤ) : Prop :=
  ∃ t : ℕ, (∀ i j : ℕ, i ≤ j → j ≤ t → p.coeff i ≤ p.coeff j) ∧
    (∀ i j : ℕ, t ≤ i → i ≤ j → p.coeff j ≤ p.coeff i)

/-- The all-size star conjecture for the polynomial defined by the delayed recurrence. -/
theorem conjecture4_1 : ∀ n : ℕ, ∀ f : Fin n → ℕ, (∀ i, f i = 1 ∨ f i = 2) →
    PolynomialUnimodal (pluckPolynomial n f) := by
  intro n f hf
  obtain ⟨t,hl,hr⟩ := sequence_unimodal n f hf
  refine ⟨t, ?_, ?_⟩
  · intro i j hij hj
    simpa only [polynomial_coeff] using hl i j hij hj
  · intro i j hi hij
    simpa only [polynomial_coeff] using hr i j hi hij

#print axioms polynomial_coeff
#print axioms uniform_unimodal
#print axioms weighted_factorial
#print axioms pluck_factorization
#print axioms conjecture4_1
end PluckingStarProof
