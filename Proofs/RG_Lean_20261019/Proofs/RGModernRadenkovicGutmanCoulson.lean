module
/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
The Coulson logarithmic integral for finite equal-trace spectra and real
Hermitian matrices, with integrability proved including zero shifted eigenvalues.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Lemma 2.4.
-/
public import Proofs.RGModernRadenkovicGutmanScalarIntegral
public import Proofs.RGModernRadenkovicGutmanSpectral

@[expose] public section

namespace Gebendorfer.RadenkovicGutman.Coulson

open Matrix Finset Set MeasureTheory
open scoped Classical
noncomputable section

variable {V : Type*} [Fintype V]

def spectralProduct (a : V → ℝ) (z : ℂ) : ℂ := ∏ i, (z - (a i : ℂ))

def logarithm (a b : V → ℝ) (t y : ℝ) : ℝ :=
  Real.log ‖spectralProduct a ((t : ℂ) + (y : ℂ) * Complex.I) /
    spectralProduct b ((t : ℂ) + (y : ℂ) * Complex.I)‖

theorem logarithm_sum (a b : V → ℝ) (t y : ℝ) (hy : 0 < y) :
    logarithm a b t y = ∑ i, Real.log
      (‖((t : ℂ) + (y : ℂ) * Complex.I) - (a i : ℂ)‖ /
        ‖((t : ℂ) + (y : ℂ) * Complex.I) - (b i : ℂ)‖) := by
  unfold logarithm spectralProduct
  rw [norm_div, norm_prod, norm_prod, Real.log_div
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (ScalarIntegral.shifted_norm_pos (a i) t y hy).ne'))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (ScalarIntegral.shifted_norm_pos (b i) t y hy).ne')),
    Real.log_prod (fun i _ => (ScalarIntegral.shifted_norm_pos (a i) t y hy).ne'),
    Real.log_prod (fun i _ => (ScalarIntegral.shifted_norm_pos (b i) t y hy).ne'),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (Real.log_div (ScalarIntegral.shifted_norm_pos (a i) t y hy).ne'
    (ScalarIntegral.shifted_norm_pos (b i) t y hy).ne').symm

theorem logarithm_integrable (a b : V → ℝ) (t : ℝ) :
    IntegrableOn (logarithm a b t) (Ioi 0) := by
  have h := integrable_finsetSum Finset.univ
    (fun i _ => ScalarIntegral.scalar_log_ratio_integrable (a i) (b i) t)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (logarithm_sum a b t y hy).symm

theorem logarithm_integral (a b : V → ℝ) (t : ℝ) :
    (∫ y : ℝ in Ioi 0, logarithm a b t y) =
      (Real.pi / 2) * (centredEnergy a t - centredEnergy b t) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => logarithm_sum a b t y hy),
    integral_finsetSum _ (fun i _ => ScalarIntegral.scalar_log_ratio_integrable (a i) (b i) t)]
  simp_rw [ScalarIntegral.scalar_log_ratio_integral]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  rfl

/-- The exact stop-loss integral at every threshold, provided the traces agree. -/
theorem stopLoss_integral (a b : V → ℝ) (ht : ∑ i, a i = ∑ i, b i) (t : ℝ) :
    (1 / Real.pi) * (∫ y : ℝ in Ioi 0, logarithm a b t y) =
      stopLoss a t - stopLoss b t := by
  rw [logarithm_integral, energy_eq_two_stopLoss_sub_trace,
    energy_eq_two_stopLoss_sub_trace, ht]
  field_simp
  ring

variable [DecidableEq V]

/-- The factorization is for the actual complexified real matrix, not a scalar proxy. -/
theorem shifted_det_product (A : Matrix V V ℝ) (hA : A.IsHermitian) (z : ℂ) :
    (z • (1 : Matrix V V ℂ) - A.map Complex.ofRealHom).det =
      spectralProduct hA.eigenvalues z := by
  rw [Matrix.smul_one_eq_diagonal, ← Matrix.scalar_apply, ← Matrix.eval_charpoly, Matrix.charpoly_map, hA.charpoly_eq]
  simp [spectralProduct, Polynomial.map_prod, Polynomial.eval_prod]

def matrixLogarithm (A B : Matrix V V ℝ) (t y : ℝ) : ℝ :=
  Real.log ‖(((t : ℂ) + (y : ℂ) * Complex.I) • (1 : Matrix V V ℂ) -
    A.map Complex.ofRealHom).det /
    (((t : ℂ) + (y : ℂ) * Complex.I) • (1 : Matrix V V ℂ) -
      B.map Complex.ofRealHom).det‖

theorem matrixLogarithm_eq (A B : Matrix V V ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (t y : ℝ) :
    matrixLogarithm A B t y = logarithm hA.eigenvalues hB.eigenvalues t y := by
  unfold matrixLogarithm logarithm
  rw [shifted_det_product A hA, shifted_det_product B hB]

theorem matrix_integrable (A B : Matrix V V ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (t : ℝ) :
    IntegrableOn (matrixLogarithm A B t) (Ioi 0) := by
  rw [show matrixLogarithm A B t = logarithm hA.eigenvalues hB.eigenvalues t from
    funext (matrixLogarithm_eq A B hA hB t)]
  exact
    logarithm_integrable hA.eigenvalues hB.eigenvalues t

theorem matrix_stopLoss_integral (A B : Matrix V V ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (ht : A.trace = B.trace) (t : ℝ) :
    (1 / Real.pi) * (∫ y : ℝ in Ioi 0, matrixLogarithm A B t y) =
      stopLoss hA.eigenvalues t - stopLoss hB.eigenvalues t := by
  simp_rw [matrixLogarithm_eq A B hA hB t]
  apply stopLoss_integral
  have ha : A.trace = ∑ i, hA.eigenvalues i := by simpa using hA.trace_eq_sum_eigenvalues
  have hb : B.trace = ∑ i, hB.eigenvalues i := by simpa using hB.trace_eq_sum_eigenvalues
  rw [← ha, ← hb, ht]

#print axioms logarithm_integrable
#print axioms shifted_det_product
#print axioms matrix_integrable
#print axioms matrix_stopLoss_integral

end
end Gebendorfer.RadenkovicGutman.Coulson
