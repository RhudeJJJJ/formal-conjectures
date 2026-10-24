module
/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Spectral counting and threshold transport for actual edge rewiring.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Lemma 2.1.
-/
public import Proofs.RGModernRadenkovicGutmanCountGap
public import Proofs.RGModernRadenkovicGutmanPerturbation

@[expose] public section

namespace Gebendorfer.RadenkovicGutman.CountGap

open Matrix Finset
open scoped InnerProductSpace Classical
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem matrix_eigen_coordinates (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (x : EuclideanSpace ℝ V) (i : V) :
    hA.eigenvectorBasis.repr (A.toEuclideanLin x) i =
      hA.eigenvalues i * hA.eigenvectorBasis.repr x i := by
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  have hs := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  rw [← hs]
  have he : A.toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  rw [he, real_inner_smul_left]

theorem rank_one_quadratic (a : V → ℝ) (x : EuclideanSpace ℝ V) :
    ⟪x, (Matrix.vecMulVec a a).toEuclideanLin x⟫_ℝ =
      ⟪WithLp.toLp 2 a, x⟫_ℝ ^ 2 := by
  simp only [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial, Matrix.vecMulVec_mulVec,
    dotProduct_smul, dotProduct_comm, op_smul_eq_smul, smul_eq_mul]
  ring

/-- The count difference is at most one for every threshold, including eigenvalues. -/
theorem rank_two_count_gap (A B : Matrix V V ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (a b : V → ℝ)
    (hdiff : A - B = Matrix.vecMulVec a a - Matrix.vecMulVec b b) (t : ℝ) :
    |aboveCount hA.eigenvalues t - aboveCount hB.eigenvalues t| ≤ 1 := by
  have hquad (x : EuclideanSpace ℝ V) :
      ⟪x, A.toEuclideanLin x⟫_ℝ - ⟪x, B.toEuclideanLin x⟫_ℝ =
        ⟪WithLp.toLp 2 a, x⟫_ℝ ^ 2 - ⟪WithLp.toLp 2 b, x⟫_ℝ ^ 2 := by
    rw [← inner_sub_right]
    have he : A.toEuclideanLin x - B.toEuclideanLin x =
        (Matrix.vecMulVec a a).toEuclideanLin x -
          (Matrix.vecMulVec b b).toEuclideanLin x := by
      have hh := congrArg (fun M : Matrix V V ℝ => M.toEuclideanLin x) hdiff
      ext i
      have hi := congrArg (fun y : EuclideanSpace ℝ V => y i) hh
      simpa only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.sub_mulVec,
        Pi.sub_apply, PiLp.sub_apply] using hi
    rw [he, inner_sub_right, rank_one_quadratic, rank_one_quadratic]
  have hAB := count_le_add_one A.toEuclideanLin B.toEuclideanLin
    hA.eigenvectorBasis hB.eigenvectorBasis hA.eigenvalues hB.eigenvalues
    (matrix_eigen_coordinates A hA) (matrix_eigen_coordinates B hB)
    (innerSL ℝ (WithLp.toLp 2 a : EuclideanSpace ℝ V)).toLinearMap
    (by
      intro x hx
      change ⟪WithLp.toLp 2 a, x⟫_ℝ = 0 at hx
      have h := hquad x
      rw [hx] at h
      nlinarith [sq_nonneg (⟪WithLp.toLp 2 b, x⟫_ℝ)]) t
  have hBA := count_le_add_one B.toEuclideanLin A.toEuclideanLin
    hB.eigenvectorBasis hA.eigenvectorBasis hB.eigenvalues hA.eigenvalues
    (matrix_eigen_coordinates B hB) (matrix_eigen_coordinates A hA)
    (innerSL ℝ (WithLp.toLp 2 b : EuclideanSpace ℝ V)).toLinearMap
    (by
      intro x hx
      change ⟪WithLp.toLp 2 b, x⟫_ℝ = 0 at hx
      have h := hquad x
      rw [hx] at h
      nlinarith [sq_nonneg (⟪WithLp.toLp 2 a, x⟫_ℝ)]) t
  have hcount (α : V → ℝ) :
      aboveCount α t = (Fintype.card {i : V // t < α i} : ℝ) := by
    simp [aboveCount, Fintype.card_subtype]
  rw [hcount, hcount, abs_le]
  have hab : (Fintype.card {i : V // t < hA.eigenvalues i} : ℝ) ≤
      Fintype.card {i : V // t < hB.eigenvalues i} + 1 := by exact_mod_cast hAB
  have hba : (Fintype.card {i : V // t < hB.eigenvalues i} : ℝ) ≤
      Fintype.card {i : V // t < hA.eigenvalues i} + 1 := by exact_mod_cast hBA
  constructor <;> linarith

theorem rewire_count_gap (G : SimpleGraph V) (u v w : V)
    (huw : u ≠ w) (hvw : v ≠ w) (hguw : ¬G.Adj u w) (hgvw : ¬G.Adj v w)
    (t : ℝ) :
    |aboveCount (laplacianSpectrum (G ⊔ SimpleGraph.edge u w)) t -
      aboveCount (laplacianSpectrum (G ⊔ SimpleGraph.edge v w)) t| ≤ 1 := by
  exact rank_two_count_gap _ _ ((G ⊔ SimpleGraph.edge u w).isHermitian_lapMatrix ℝ)
    ((G ⊔ SimpleGraph.edge v w).isHermitian_lapMatrix ℝ) (edgeVector u w) (edgeVector v w)
    (rewire_laplacian_difference G u v w huw hvw hguw hgvw) t

/-- The dimension-free transport estimate now has no spectral-count premise. -/
theorem rewire_stopLoss_transport (G : SimpleGraph V) (u v w : V)
    (huw : u ≠ w) (hvw : v ≠ w) (hguw : ¬G.Adj u w) (hgvw : ¬G.Adj v w)
    (s t : ℝ) :
    |(stopLoss (laplacianSpectrum (G ⊔ SimpleGraph.edge u w)) s -
        stopLoss (laplacianSpectrum (G ⊔ SimpleGraph.edge v w)) s) -
      (stopLoss (laplacianSpectrum (G ⊔ SimpleGraph.edge u w)) t -
        stopLoss (laplacianSpectrum (G ⊔ SimpleGraph.edge v w)) t)| ≤ |s - t| :=
  stopLoss_difference_lipschitz _ _
    (rewire_count_gap G u v w huw hvw hguw hgvw) s t

theorem rewire_mean_transport (G : SimpleGraph V) (u v w : V)
    (huw : u ≠ w) (hvw : v ≠ w) (hguw : ¬G.Adj u w) (hgvw : ¬G.Adj v w) :
    let n : ℝ := Fintype.card V
    let D := fun t => stopLoss (laplacianSpectrum (G ⊔ SimpleGraph.edge u w)) t -
      stopLoss (laplacianSpectrum (G ⊔ SimpleGraph.edge v w)) t
    D 2 - 2 / n ≤ D (2 - 2 / n) := by
  dsimp only
  have h := rewire_stopLoss_transport G u v w huw hvw hguw hgvw
    (2 - 2 / (Fintype.card V : ℝ)) 2
  have he : |(2 - 2 / (Fintype.card V : ℝ)) - 2| =
      2 / (Fintype.card V : ℝ) := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
  rw [he, abs_le] at h
  linarith [h.1]

#print axioms rank_two_count_gap
#print axioms rewire_count_gap
#print axioms rewire_stopLoss_transport
#print axioms rewire_mean_transport

end
end Gebendorfer.RadenkovicGutman.CountGap
