module
/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Nonreal spectral parameters give genuine inverses of the path Laplacian.
The global energy and strict fusion inequalities are not asserted here.
-/
public import Proofs.RGModernRadenkovicGutmanPathDeterminant
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

namespace Gebendorfer.RadenkovicGutman.PathRecurrence

open Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact characteristic factorization evaluated away from the real spectrum. -/
theorem shifted_det_product (A : Matrix V V ℂ) (hA : A.IsHermitian) (z : ℂ) :
    det (z • (1 : Matrix V V ℂ) - A) =
      ∏ i, (z - (hA.eigenvalues i : ℂ)) := by
  have h := congrArg (fun p : Polynomial ℂ => p.eval z) hA.charpoly_eq
  simpa [Matrix.eval_charpoly, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal, Polynomial.eval_prod]
    using h

/-- Every nonreal shift of a finite Hermitian matrix has nonzero determinant. -/
theorem shifted_det_ne_zero (A : Matrix V V ℂ) (hA : A.IsHermitian)
    (z : ℂ) (hz : z.im ≠ 0) :
    det (z • (1 : Matrix V V ℂ) - A) ≠ 0 := by
  rw [shifted_det_product A hA z]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ hi
  have he := congrArg Complex.im (sub_eq_zero.mp hi)
  exact hz (by simpa using he)

/-- The scalar denominator is nonzero at every nonreal spectral parameter. -/
theorem den_ne_zero_of_im_ne_zero (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    den z (n + 1) ≠ 0 := by
  rw [← pathMatrix_det]
  exact shifted_det_ne_zero _ ((SimpleGraph.pathGraph (n + 1)).isHermitian_lapMatrix ℂ) z hz

theorem pathMatrix_mul_inverse (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    pathMatrix z (n + 1) * (pathMatrix z (n + 1))⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  rw [pathMatrix_det]
  exact isUnit_iff_ne_zero.mpr (den_ne_zero_of_im_ne_zero z hz n)

/-- Endpoint entry and recurrence now concern genuine graph resolvents. -/
theorem endpoint_resolvent_recurrence (z : ℂ) (hz : z.im ≠ 0) (n : ℕ) :
    (pathMatrix z (n + 2))⁻¹ 0 0 =
      (1 - (pathMatrix z (n + 1))⁻¹ 0 0) /
        (z - 1 - z * (pathMatrix z (n + 1))⁻¹ 0 0) := by
  rw [pathMatrix_inv_endpoint, pathMatrix_inv_endpoint]
  exact resolventQuotient_succ z (n + 1) (den_ne_zero_of_im_ne_zero z hz n)

#print axioms shifted_det_ne_zero
#print axioms den_ne_zero_of_im_ne_zero
#print axioms pathMatrix_mul_inverse
#print axioms endpoint_resolvent_recurrence

end Gebendorfer.RadenkovicGutman.PathRecurrence
