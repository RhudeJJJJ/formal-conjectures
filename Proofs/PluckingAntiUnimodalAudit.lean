/-
Copyright 2026 Jonas J. Gebendorfer.
Licensed under the Apache License, Version 2.0.
-/
import Proofs.PluckingAntiUnimodalProof

namespace PluckingAntiUnimodalAudit
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def Valid {n : ℕ} (parent : Fin n → Option (Fin n)) : Prop :=
  ∀ v w, parent v = some w → w.val < v.val

def ancestors {n : ℕ} (parent : Fin n → Option (Fin n)) : ℕ → Fin n → Finset (Fin n)
  | 0, _ => ∅
  | k+1, v => insert v (match parent v with | none => ∅ | some w => ancestors parent k w)

def PreorderLabels {n : ℕ} (p : Fin n → Option (Fin n)) : Prop :=
  ∀ a b c, a ∈ ancestors p n b → a ≤ c → c ≤ b → a ∈ ancestors p n c

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

def nextDelay {n : ℕ} (p : Fin n → Option (Fin n)) (s : Finset (Fin n))
    (f : Fin n → ℕ) (w : Fin n) : ℕ :=
  if IsLeaf p s w then max 1 (f w - 1) else 1

noncomputable def polynomial {n : ℕ} (p : Fin n → Option (Fin n)) :
    ℕ → Finset (Fin n) → (Fin n → ℕ) → Polynomial ℤ
  | 0, s, _ => if s = ∅ then 1 else 0
  | k+1, s, f => if s = ∅ then 1 else
      ∑ v ∈ eligible p s f, Polynomial.X ^ rightCount p s v *
        polynomial p k (s.erase v) (nextDelay p s f)

def PolynomialUnimodal (P : Polynomial ℤ) : Prop :=
  ∃ t : ℕ, (∀ i j : ℕ, i ≤ j → j ≤ t → P.coeff i ≤ P.coeff j) ∧
    (∀ i j : ℕ, t ≤ i → i ≤ j → P.coeff j ≤ P.coeff i)

def AntiUnimodal {m : ℕ} (a : Fin m → ℕ) : Prop :=
  ∃ t : Fin m, (∀ i j, i ≤ j → j ≤ t → a j ≤ a i) ∧
    (∀ i j, t ≤ i → i ≤ j → a i ≤ a j)

theorem ancestors_eq {n : ℕ} (p : Fin n → Option (Fin n)) (k : ℕ) :
    ancestors p k = PluckingAntiUnimodalProof.ancestors p k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext v
    simp only [ancestors,PluckingAntiUnimodalProof.ancestors]
    cases p v <;> simp only [ih]

theorem rightOf_eq {n : ℕ} (p : Fin n → Option (Fin n)) (x y : Fin n) :
    RightOf p x y = PluckingAntiUnimodalProof.RightOf p x y := by
  simp only [RightOf,PluckingAntiUnimodalProof.RightOf,ancestors_eq]

theorem rightCount_eq {n : ℕ} (p : Fin n → Option (Fin n)) (s : Finset (Fin n)) (v : Fin n) :
    rightCount p s v = PluckingAntiUnimodalProof.rightCount p s v := by
  simp only [rightCount,PluckingAntiUnimodalProof.rightCount,rightOf_eq]

theorem polynomial_eq {n : ℕ} (p : Fin n → Option (Fin n)) (k : ℕ)
    (s : Finset (Fin n)) (f : Fin n → ℕ) :
    polynomial p k s f = PluckingAntiUnimodalProof.polynomial p k s f := by
  induction k generalizing s f with
  | zero => rfl
  | succ k ih =>
    simp only [polynomial,PluckingAntiUnimodalProof.polynomial]
    split_ifs
    · rfl
    · apply sum_congr rfl
      intro v _
      rw [rightCount_eq,ih]
      rfl

theorem exact_statement : False ↔ ∀ (n : ℕ) (p : Fin n → Option (Fin n)), Valid p → PreorderLabels p →
      ∀ f : Fin n → ℕ, (∀ v, 0 < f v) →
      ∀ (m : ℕ) (order : Fin m → Fin n), StrictMono order →
        Finset.univ.image order = Finset.univ.filter (IsLeaf p Finset.univ) →
        AntiUnimodal (f ∘ order) → PolynomialUnimodal (polynomial p n Finset.univ f) := by
  refine ⟨False.elim,fun h => PluckingAntiUnimodalProof.open_problem4_2 ?_⟩
  intro n p hv hp f hf m order ho hl ha
  have hpre : PreorderLabels p := by
    simpa only [PreorderLabels,PluckingAntiUnimodalProof.PreorderLabels,ancestors_eq] using hp
  have hh := h n p hv hpre f hf m order ho hl ha
  change PolynomialUnimodal (PluckingAntiUnimodalProof.polynomial p n univ f)
  rw [← polynomial_eq]
  exact hh

#print axioms PluckingAntiUnimodalProof.valid_witness
#print axioms PluckingAntiUnimodalProof.preorder_witness
#print axioms PluckingAntiUnimodalProof.initial_leaves
#print axioms PluckingAntiUnimodalProof.ordered_initial_leaves
#print axioms PluckingAntiUnimodalProof.positive_delays
#print axioms PluckingAntiUnimodalProof.anti_unimodal
#print axioms PluckingAntiUnimodalProof.polynomial_coeff
#print axioms PluckingAntiUnimodalProof.operational_recurrence
#print axioms PluckingAntiUnimodalProof.coefficient10
#print axioms PluckingAntiUnimodalProof.coefficient11
#print axioms PluckingAntiUnimodalProof.coefficient12
#print axioms PluckingAntiUnimodalProof.not_unimodal
#print axioms PluckingAntiUnimodalProof.open_problem4_2
#print axioms exact_statement
#print axioms ancestors_eq
#print axioms polynomial_eq
end PluckingAntiUnimodalAudit
