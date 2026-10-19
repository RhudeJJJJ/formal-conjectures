/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The actual graph-root resolvent and its principal-minor Schur complement.
The principal minor retains the degrees in the original core graph.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Section 3.1.
-/
import Proofs.RadenkovicGutmanFusionQuotient
import Proofs.RadenkovicGutmanReciprocalDisk

namespace Gebendorfer.RadenkovicGutman.RootSchur

open Matrix Finset
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Rest (u : V) := {v : V // v ≠ u}

def principalLaplacian (C : SimpleGraph V) (u : V) : Matrix (Rest u) (Rest u) ℂ :=
  (C.lapMatrix ℂ).submatrix Subtype.val Subtype.val

def rootNeighbors (C : SimpleGraph V) (u : V) : Rest u → ℂ :=
  fun v => if C.Adj u v then 1 else 0

def schurScalar (C : SimpleGraph V) (u : V) (z : ℂ) : ℂ :=
  z - (C.degree u : ℂ) - star (rootNeighbors C u) ⬝ᵥ
    ((z • (1 : Matrix (Rest u) (Rest u) ℂ) - principalLaplacian C u)⁻¹ *ᵥ
      rootNeighbors C u)

theorem principal_isHermitian (C : SimpleGraph V) (u : V) :
    (principalLaplacian C u).IsHermitian :=
  (C.isHermitian_lapMatrix ℂ).submatrix Subtype.val

omit [Fintype V] [DecidableEq V] in
theorem rootNeighbors_star (C : SimpleGraph V) (u : V) :
    star (rootNeighbors C u) = rootNeighbors C u := by
  ext v
  simp [rootNeighbors]

theorem rootNeighbors_norm (C : SimpleGraph V) (u : V) :
    ‖(WithLp.toLp 2 (rootNeighbors C u) : EuclideanSpace ℂ (Rest u))‖ ^ 2 =
      (C.degree u : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [rootNeighbors]
  simp_rw [show ∀ v : Rest u, ‖(if C.Adj u v then (1 : ℂ) else 0)‖ ^ 2 =
    (if C.Adj u v then (1 : ℝ) else 0) from fun v => by split_ifs <;> norm_num]
  have hs : (∑ v : Rest u, if C.Adj u v then (1 : ℝ) else 0) = C.degree u := by
    have hfull := Fintype.sum_eq_add_sum_subtype_ne
      (fun v : V => if C.Adj u v then (1 : ℝ) else 0) u
    have hdeg : (∑ v : V, if C.Adj u v then (1 : ℝ) else 0) = C.degree u := by
      simp only [Finset.sum_boole, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
    simpa using hfull.symm.trans hdeg
  simpa using hs

theorem shifted_principal (C : SimpleGraph V) (u : V) (z : ℂ) :
    (CoreQuotient.shifted z C).submatrix (fun v : Rest u => v.val) Subtype.val =
      z • (1 : Matrix (Rest u) (Rest u) ℂ) - principalLaplacian C u := by
  ext i j
  simp [CoreQuotient.shifted, principalLaplacian, Matrix.submatrix_apply,
    Matrix.one_apply, Subtype.val_inj]

/-- The inverse's genuine root diagonal is the inverse Schur scalar. -/
theorem root_resolvent_schur (C : SimpleGraph V) (u : V) (z : ℂ)
    (hz : 0 < z.im) :
    CoreQuotient.rootResolvent z C u = (schurScalar C u z)⁻¹ := by
  let M := CoreQuotient.shifted z C
  let R := z • (1 : Matrix (Rest u) (Rest u) ℂ) - principalLaplacian C u
  let b := rootNeighbors C u
  let x : V → ℂ := fun v => M⁻¹ v u
  let k := x u
  have hM : IsUnit M.det := CoreQuotient.shifted_isUnit z hz.ne' C
  have hR : IsUnit R.det := isUnit_iff_ne_zero.mpr
    (PathRecurrence.shifted_det_ne_zero _ (principal_isHermitian C u) z hz.ne')
  have hMx (i : V) : (M *ᵥ x) i = if i = u then 1 else 0 := by
    exact congrArg (fun N : Matrix V V ℂ => N i u) (Matrix.mul_nonsing_inv M hM)
  have hdiag : M u u = z - (C.degree u : ℂ) := by
    simp [M, CoreQuotient.shifted, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      SimpleGraph.adjMatrix_apply]
  have hrow (v : Rest u) : M u v = b v := by
    simp [M, CoreQuotient.shifted, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      SimpleGraph.adjMatrix_apply, b, rootNeighbors, v.property.symm]
  have hcol (v : Rest u) : M v u = b v := by
    simp [M, CoreQuotient.shifted, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      SimpleGraph.adjMatrix_apply, b, rootNeighbors, v.property, C.adj_comm]
  have hrest : R *ᵥ (fun v : Rest u => x v) = -(k • b) := by
    ext i
    have hi := hMx i
    rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_add_sum_subtype_ne _ u] at hi
    rw [hcol, if_neg i.property] at hi
    have he : (R *ᵥ (fun v : Rest u => x v)) i =
        ∑ j : Rest u, M i j * x j := by
      change (∑ j : Rest u, R i j * x j) = _
      apply Finset.sum_congr rfl
      intro j _
      have hh := congrArg (fun N : Matrix (Rest u) (Rest u) ℂ => N i j)
        (shifted_principal C u z)
      exact congrArg (fun a : ℂ => a * x j) hh.symm
    rw [he]
    change _ = -(k * b i)
    dsimp only [k]
    linear_combination hi
  have hx : (fun v : Rest u => x v) = -(k • (R⁻¹ *ᵥ b)) := by
    have hh := congrArg (fun v => R⁻¹ *ᵥ v) hrest
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul R hR, Matrix.one_mulVec,
      Matrix.mulVec_neg, Matrix.mulVec_smul] at hh
    exact hh
  have hroot := hMx u
  rw [Matrix.mulVec, dotProduct, Fintype.sum_eq_add_sum_subtype_ne _ u,
    hdiag, if_pos rfl] at hroot
  have hsum : (∑ j : Rest u, M u j * x j) =
      -(k * (b ⬝ᵥ (R⁻¹ *ᵥ b))) := by
    simp_rw [hrow]
    change b ⬝ᵥ (fun j : Rest u => x j) = _
    rw [hx, dotProduct_neg, dotProduct_smul]
    rfl
  rw [hsum] at hroot
  have hprod : schurScalar C u z * k = 1 := by
    unfold schurScalar
    rw [rootNeighbors_star]
    change (z - (C.degree u : ℂ) - b ⬝ᵥ (R⁻¹ *ᵥ b)) * k = 1
    dsimp only [k] at hroot ⊢
    linear_combination hroot
  exact (inv_eq_of_mul_eq_one_right hprod).symm

/-- The graph-theoretic Schur scalar satisfies the degree-specific disk bound. -/
theorem graph_schur_disk (C : SimpleGraph V) (u : V) (z : ℂ)
    (hz : 0 < z.im) :
    ‖schurScalar C u z -
        (z - (C.degree u : ℂ) + (C.degree u / (2 * z.im) : ℝ) * Complex.I)‖ ≤
      (C.degree u : ℝ) / (2 * z.im) ∧ z.im ≤ (schurScalar C u z).im := by
  have h := ResolventDisk.schur_complement_disk (principalLaplacian C u)
    (principal_isHermitian C u) z hz (C.degree u) (rootNeighbors C u)
  simpa only [rootNeighbors_norm, schurScalar, Complex.ofReal_natCast] using h

/-- The explicit k-plane disk is now attached to the actual core Laplacian. -/
theorem graph_root_disk (C : SimpleGraph V) (u : V) (y : ℝ) (hy : 0 < y) :
    let d : ℝ := C.degree u
    let Δ := (d - 2) ^ 2 + d + y ^ 2
    let c : ℂ := ((2 - d) / Δ : ℝ) - ((2 * y ^ 2 + d) / (2 * y * Δ) : ℝ) * Complex.I
    let R : ℝ := d / (2 * y * Δ)
    CoreQuotient.rootResolvent (2 + (y : ℂ) * Complex.I) C u ≠ 0 ∧
      ‖CoreQuotient.rootResolvent (2 + (y : ℂ) * Complex.I) C u - c‖ ≤ R ∧
      Complex.normSq c - R ^ 2 = 1 / Δ := by
  dsimp only
  have hz : 0 < (2 + (y : ℂ) * Complex.I).im := by simpa using hy
  have h := graph_schur_disk C u (2 + (y : ℂ) * Complex.I) hz
  have hd := ResolventDisk.reciprocal_schur_disk (C.degree u) y
    (by positivity) hy (schurScalar C u (2 + (y : ℂ) * Complex.I))
    (by convert h.1 using 2 <;> simp [sub_add_eq_add_sub, add_assoc, add_mul])
  rw [root_resolvent_schur C u _ hz]
  exact ⟨inv_ne_zero hd.1, hd.2⟩

#print axioms rootNeighbors_norm
#print axioms root_resolvent_schur
#print axioms graph_schur_disk
#print axioms graph_root_disk

end
end Gebendorfer.RadenkovicGutman.RootSchur
