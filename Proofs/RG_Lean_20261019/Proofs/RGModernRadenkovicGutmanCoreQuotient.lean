module
/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.

Finite-rank determinant reduction for an arbitrary residual core.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Section 2.2. These are algebraic identities, not the
analytic strict fusion inequality.
-/
public import Proofs.RGModernRadenkovicGutmanPathResolvent
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Gebendorfer.RadenkovicGutman.CoreQuotient

open Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K : Type*} [Field K]

/-- Incidence vector, with arbitrary coefficient field. -/
def incidence (u v : V) : V → K :=
  fun i => (if i = u then 1 else 0) - (if i = v then 1 else 0)

theorem incidence_dot (u v : V) (x : V → K) :
    incidence u v ⬝ᵥ x = x u - x v := by
  unfold incidence dotProduct
  simp_rw [sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib]
  simp

theorem mulVec_incidence (A : Matrix V V K) (u v : V) (i : V) :
    (A *ᵥ incidence u v) i = A i u - A i v := by
  unfold incidence mulVec dotProduct
  simp_rw [mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_sub_distrib]
  simp

/-- The rank-two determinant lemma, without assumptions on the two vectors. -/
theorem det_sub_two (A : Matrix V V K) (hA : IsUnit A.det) (u v : V → K) :
    det (A - vecMulVec u u - vecMulVec v v) =
      det A * ((1 - u ⬝ᵥ (A⁻¹ *ᵥ u)) * (1 - v ⬝ᵥ (A⁻¹ *ᵥ v)) -
        (u ⬝ᵥ (A⁻¹ *ᵥ v)) * (v ⬝ᵥ (A⁻¹ *ᵥ u))) := by
  let U : Matrix V (Fin 2) K := fun i => ![u i, v i]
  have hUV : A - vecMulVec u u - vecMulVec v v = A + (-U) * U.transpose := by
    ext i j
    change A i j - u i * u j - v i * v j =
      A i j + ∑ k : Fin 2, (-U i k) * U j k
    rw [Fin.sum_univ_two]
    change A i j - u i * u j - v i * v j =
      A i j + ((-u i) * u j + (-v i) * v j)
    ring
  rw [hUV, Matrix.det_add_mul (-U) U.transpose hA, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.mul_neg]
  have hentry (i j : Fin 2) :
      (U.transpose * A⁻¹ * U) i j =
        (fun k => U k i) ⬝ᵥ (A⁻¹ *ᵥ (fun k => U k j)) := by
    rw [Matrix.mul_assoc]
    rfl
  simp only [Matrix.neg_apply, hentry]
  simp [U, sub_eq_add_neg]

/-- One edge added between two components; the mixed inverse entries vanish. -/
theorem det_sub_edge (A : Matrix V V K) (hA : IsUnit A.det) (u v : V)
    (huv : A⁻¹ u v = 0) (hvu : A⁻¹ v u = 0) :
    det (A - vecMulVec (incidence u v) (incidence u v)) =
      det A * (1 - A⁻¹ u u - A⁻¹ v v) := by
  have h := det_sub_two A hA (incidence u v) 0
  simpa [incidence_dot, mulVec_incidence, huv, hvu, sub_add_eq_sub_sub]
    using h

/-- Two root edges added to three separate components. -/
theorem det_sub_two_root_edges (A : Matrix V V K) (hA : IsUnit A.det)
    (u v w : V)
    (huv : A⁻¹ u v = 0) (hvu : A⁻¹ v u = 0)
    (huw : A⁻¹ u w = 0) (hwu : A⁻¹ w u = 0)
    (hvw : A⁻¹ v w = 0) (hwv : A⁻¹ w v = 0) :
    det (A - vecMulVec (incidence u v) (incidence u v) -
      vecMulVec (incidence u w) (incidence u w)) =
      det A * ((1 - A⁻¹ v v) * (1 - A⁻¹ w w) -
        A⁻¹ u u * (2 - A⁻¹ v v - A⁻¹ w w)) := by
  rw [det_sub_two A hA]
  simp only [incidence_dot, mulVec_incidence, huv, hvu, huw, hwu, hvw, hwv,
    sub_zero, zero_sub]
  ring

#print axioms det_sub_two
#print axioms det_sub_edge
#print axioms det_sub_two_root_edges

variable {W X : Type*} [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X]

theorem blockDiagonal_inverse (A : Matrix V V K) (B : Matrix W W K)
    (hA : IsUnit A.det) (hB : IsUnit B.det) :
    (fromBlocks A 0 0 B)⁻¹ = fromBlocks A⁻¹ 0 0 B⁻¹ := by
  have hAB : IsUnit A ↔ IsUnit B := by
    constructor <;> intro _
    · exact (Matrix.isUnit_iff_isUnit_det B).mpr hB
    · exact (Matrix.isUnit_iff_isUnit_det A).mpr hA
  simpa using Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff A 0 B hAB

/-- Three independent components, before the root edges are inserted. -/
def forestMatrix (C : Matrix V V K) (P : Matrix W W K) (Q : Matrix X X K) :
    Matrix (V ⊕ W ⊕ X) (V ⊕ W ⊕ X) K :=
  fromBlocks C 0 0 (fromBlocks P 0 0 Q)

theorem forest_det (C : Matrix V V K) (P : Matrix W W K) (Q : Matrix X X K) :
    (forestMatrix C P Q).det = C.det * P.det * Q.det := by
  simp [forestMatrix, mul_assoc]

theorem forest_inverse (C : Matrix V V K) (P : Matrix W W K) (Q : Matrix X X K)
    (hC : IsUnit C.det) (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    (forestMatrix C P Q)⁻¹ = forestMatrix C⁻¹ P⁻¹ Q⁻¹ := by
  unfold forestMatrix
  rw [blockDiagonal_inverse C _ hC (by simpa using hP.mul hQ),
    blockDiagonal_inverse P Q hP hQ]

/-- The raw two-arm determinant formula, valid for every finite core matrix. -/
theorem rooted_two_arm_det (C : Matrix V V K) (P : Matrix W W K) (Q : Matrix X X K)
    (hC : IsUnit C.det) (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (u : V) (v : W) (w : X) :
    det (forestMatrix C P Q -
      vecMulVec (incidence (.inl u) (.inr (.inl v)))
        (incidence (.inl u) (.inr (.inl v))) -
      vecMulVec (incidence (.inl u) (.inr (.inr w)))
        (incidence (.inl u) (.inr (.inr w)))) =
      C.det * P.det * Q.det *
        ((1 - P⁻¹ v v) * (1 - Q⁻¹ w w) - C⁻¹ u u * (2 - P⁻¹ v v - Q⁻¹ w w)) := by
  have hf : IsUnit (forestMatrix C P Q).det := by
    rw [forest_det]
    exact (hC.mul hP).mul hQ
  rw [det_sub_two_root_edges _ hf (.inl u) (.inr (.inl v)) (.inr (.inr w))]
  all_goals rw [forest_inverse C P Q hC hP hQ]
  all_goals simp [forestMatrix, mul_assoc]

/-- The raw one-arm formula, valid for every finite core matrix. -/
theorem rooted_one_arm_det (C : Matrix V V K) (P : Matrix W W K)
    (hC : IsUnit C.det) (hP : IsUnit P.det) (u : V) (v : W) :
    det (fromBlocks C 0 0 P -
      vecMulVec (incidence (.inl u) (.inr v)) (incidence (.inl u) (.inr v))) =
      C.det * P.det * (1 - C⁻¹ u u - P⁻¹ v v) := by
  have hf : IsUnit (fromBlocks C 0 0 P).det := by simpa using hC.mul hP
  rw [det_sub_edge _ hf (.inl u) (.inr v)]
  all_goals simp [blockDiagonal_inverse C P hC hP]

#print axioms rooted_two_arm_det
#print axioms rooted_one_arm_det

end Gebendorfer.RadenkovicGutman.CoreQuotient
