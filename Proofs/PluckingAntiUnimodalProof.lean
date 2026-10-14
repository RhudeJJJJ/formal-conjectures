/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Mathlib.Tactic

namespace PluckingAntiUnimodalProof
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The root is implicit. Nonroot vertices have a smaller parent, or the root as parent.
Children are ordered by their labels. This is a finite plane rooted tree representation. -/
def Valid {n : ℕ} (parent : Fin n → Option (Fin n)) : Prop :=
  ∀ v w, parent v = some w → w.val < v.val

def ancestors {n : ℕ} (parent : Fin n → Option (Fin n)) : ℕ → Fin n → Finset (Fin n)
  | 0, _ => ∅
  | k+1, v => insert v (match parent v with | none => ∅ | some w => ancestors parent k w)

/-- The descendant labels of every vertex are consecutive: labels are depth-first preorder. -/
def PreorderLabels {n : ℕ} (p : Fin n → Option (Fin n)) : Prop :=
  ∀ a b c, a ∈ ancestors p n b → a ≤ c → c ≤ b → a ∈ ancestors p n c

/-- An edge entering y is right of the root path to x exactly when their paths use
ordered distinct sibling branches at some common parent. Attachment edges are included. -/
def RightOf {n : ℕ} (parent : Fin n → Option (Fin n)) (x y : Fin n) : Prop :=
  ∃ a ∈ ancestors parent n x, ∃ b ∈ ancestors parent n y,
    parent a = parent b ∧ a.val < b.val

instance {n : ℕ} (p : Fin n → Option (Fin n)) (x y : Fin n) : Decidable (RightOf p x y) :=
  inferInstanceAs (Decidable (∃ a ∈ ancestors p n x, ∃ b ∈ ancestors p n y,
    p a = p b ∧ a.val < b.val))

def IsLeaf {n : ℕ} (parent : Fin n → Option (Fin n)) (live : Finset (Fin n)) (v : Fin n) : Prop :=
  v ∈ live ∧ ∀ w ∈ live, parent w ≠ some v

instance {n : ℕ} (p : Fin n → Option (Fin n)) (s : Finset (Fin n)) (v : Fin n) :
    Decidable (IsLeaf p s v) := inferInstanceAs (Decidable (v ∈ s ∧ ∀ w ∈ s, p w ≠ some v))

def eligible {n : ℕ} (p : Fin n → Option (Fin n)) (s : Finset (Fin n)) (f : Fin n → ℕ) :
    Finset (Fin n) := s.filter fun v => IsLeaf p s v ∧ f v = 1

def rightCount {n : ℕ} (p : Fin n → Option (Fin n)) (s : Finset (Fin n)) (v : Fin n) : ℕ :=
  (s.filter fun w => RightOf p v w).card

/-- Surviving old leaves decrement; newly exposed leaves receive delay one. -/
def nextDelay {n : ℕ} (p : Fin n → Option (Fin n)) (s : Finset (Fin n))
    (f : Fin n → ℕ) (w : Fin n) : ℕ :=
  if IsLeaf p s w then max 1 (f w - 1) else 1

def oneSeq (j : ℤ) : ℤ := if j = 0 then 1 else 0

/-- Coefficients of the operational delayed-pluck recurrence, with at most fuel removals. -/
def coefficient {n : ℕ} (p : Fin n → Option (Fin n)) :
    ℕ → Finset (Fin n) → (Fin n → ℕ) → ℤ → ℤ
  | 0, s, _, j => if s = ∅ then oneSeq j else 0
  | k+1, s, f, j => if s = ∅ then oneSeq j else
      ∑ v ∈ eligible p s f, coefficient p k (s.erase v) (nextDelay p s f) (j-rightCount p s v)

noncomputable def polynomial {n : ℕ} (p : Fin n → Option (Fin n)) :
    ℕ → Finset (Fin n) → (Fin n → ℕ) → Polynomial ℤ
  | 0, s, _ => if s = ∅ then 1 else 0
  | k+1, s, f => if s = ∅ then 1 else
      ∑ v ∈ eligible p s f, Polynomial.X ^ rightCount p s v *
        polynomial p k (s.erase v) (nextDelay p s f)

theorem coefficient_negative {n : ℕ} (p : Fin n → Option (Fin n)) (k : ℕ)
    (s : Finset (Fin n)) (f : Fin n → ℕ) (j : ℤ) (hj : j < 0) :
    coefficient p k s f j = 0 := by
  induction k generalizing s f j with
  | zero => simp [coefficient,oneSeq,show j ≠ 0 by omega]
  | succ k ih =>
    rw [coefficient]
    split_ifs
    · simp [oneSeq,show j ≠ 0 by omega]
    · apply sum_eq_zero; intro v _; exact ih _ _ _ (by omega)

theorem polynomial_coeff {n : ℕ} (p : Fin n → Option (Fin n)) (k : ℕ)
    (s : Finset (Fin n)) (f : Fin n → ℕ) (j : ℕ) :
    (polynomial p k s f).coeff j = coefficient p k s f j := by
  induction k generalizing s f j with
  | zero => by_cases hs : s = ∅ <;> simp [polynomial,coefficient,hs,oneSeq,Polynomial.coeff_one]
  | succ k ih =>
    rw [polynomial,coefficient]
    split_ifs
    · simp [oneSeq,Polynomial.coeff_one]
    · rw [Polynomial.finsetSum_coeff]
      apply sum_congr rfl
      intro v _
      rw [Polynomial.coeff_X_pow_mul']
      by_cases hj : rightCount p s v ≤ j
      · rw [if_pos hj,ih]
        congr 1
        omega
      · rw [if_neg hj]
        exact (coefficient_negative _ _ _ _ _ (by omega)).symm

/-- Fuel is sufficient: every recursive branch deletes a present vertex. This identity
is the unfuelled recurrence on exact cardinalities, not an asymptotic cutoff. -/
theorem operational_recurrence {n : ℕ} (p : Fin n → Option (Fin n))
    (s : Finset (Fin n)) (f : Fin n → ℕ) (hs : s.Nonempty) :
    polynomial p s.card s f = ∑ v ∈ eligible p s f,
      Polynomial.X ^ rightCount p s v * polynomial p (s.erase v).card (s.erase v) (nextDelay p s f) := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_ne_zero.mpr hs)
  rw [hk,polynomial,if_neg (Finset.nonempty_iff_ne_empty.mp hs)]
  apply sum_congr rfl
  intro v hv
  have hv' : v ∈ s := (Finset.mem_filter.mp hv).1
  have he : (s.erase v).card = k := by rw [Finset.card_erase_of_mem hv',hk]; omega
  rw [he]

def PolynomialUnimodal (P : Polynomial ℤ) : Prop :=
  ∃ t : ℕ, (∀ i j : ℕ, i ≤ j → j ≤ t → P.coeff i ≤ P.coeff j) ∧
    (∀ i j : ℕ, t ≤ i → i ≤ j → P.coeff j ≤ P.coeff i)

/-- Leaves are read from left to right in this concrete preorder. -/
def witnessParent : Fin 8 → Option (Fin 8) :=
  ![none,some 0,none,some 2,some 3,some 3,some 5,some 5]
def witnessDelay : Fin 8 → ℕ := ![1,1,1,1,1,1,2,3]

theorem valid_witness : Valid witnessParent := by unfold Valid; decide
theorem preorder_witness : PreorderLabels witnessParent := by unfold PreorderLabels; decide
theorem initial_leaves : Finset.univ.filter (IsLeaf witnessParent Finset.univ) = {1,4,6,7} := by decide
theorem positive_delays : ∀ v, 0 < witnessDelay v := by decide

/-- Anti-unimodality for the ordered initial leaves, including an endpoint minimum. -/
def AntiUnimodal {m : ℕ} (a : Fin m → ℕ) : Prop :=
  ∃ t : Fin m, (∀ i j, i ≤ j → j ≤ t → a j ≤ a i) ∧
    (∀ i j, t ≤ i → i ≤ j → a i ≤ a j)
def leafOrder : Fin 4 → Fin 8 := ![1,4,6,7]
theorem ordered_initial_leaves :
    (Finset.univ.image leafOrder = {1,4,6,7}) ∧ StrictMono leafOrder := by decide
theorem anti_unimodal : AntiUnimodal (witnessDelay ∘ leafOrder) := by unfold AntiUnimodal; decide

noncomputable def witnessPolynomial : Polynomial ℤ :=
  polynomial witnessParent 8 Finset.univ witnessDelay

theorem coefficient10 : witnessPolynomial.coeff 10 = 9 := by
  rw [witnessPolynomial,polynomial_coeff]
  decide
theorem coefficient11 : witnessPolynomial.coeff 11 = 8 := by
  rw [witnessPolynomial,polynomial_coeff]
  decide
theorem coefficient12 : witnessPolynomial.coeff 12 = 9 := by
  rw [witnessPolynomial,polynomial_coeff]
  decide

theorem not_unimodal : ¬ PolynomialUnimodal witnessPolynomial := by
  rintro ⟨t,hl,hr⟩
  by_cases ht : 11 ≤ t
  · have h := hl 10 11 (by omega) ht
    rw [coefficient10,coefficient11] at h
    omega
  · have h := hr 11 12 (by omega) (by omega)
    rw [coefficient11,coefficient12] at h
    omega

/-- Negative answer to the general plane-rooted-tree Open Problem 4.2. -/
theorem open_problem4_2 :
    ¬ ∀ (n : ℕ) (p : Fin n → Option (Fin n)), Valid p → PreorderLabels p →
      ∀ f : Fin n → ℕ, (∀ v, 0 < f v) →
      ∀ (m : ℕ) (order : Fin m → Fin n), StrictMono order →
        Finset.univ.image order = Finset.univ.filter (IsLeaf p Finset.univ) →
        AntiUnimodal (f ∘ order) → PolynomialUnimodal (polynomial p n Finset.univ f) := by
  intro h
  apply not_unimodal
  exact h 8 witnessParent valid_witness preorder_witness witnessDelay positive_delays
    4 leafOrder ordered_initial_leaves.2
    (ordered_initial_leaves.1.trans initial_leaves.symm) anti_unimodal

#print axioms polynomial_coeff
#print axioms operational_recurrence
#print axioms not_unimodal
#print axioms open_problem4_2
end PluckingAntiUnimodalProof
