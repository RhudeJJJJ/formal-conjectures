/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRationalPolynomialCell
import Proofs.RadenkovicGutmanClassScalarIntegrals
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Gebendorfer.RadenkovicGutman.BernsteinLogIntegral

open Finset Set MeasureTheory
open scoped Classical
noncomputable section

variable {J : Type*} [Fintype J]

theorem weighted_log_lower (w c : J → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (hc : ∀ i, 0 < c i) :
    ∑ i, w i * Real.log (c i) ≤ Real.log (∑ i, w i * c i) := by
  simpa only [smul_eq_mul] using
    strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := Finset.univ)
      (w := w) (p := c) (fun i _ => hw i) hs (fun i _ => hc i)

theorem log_tangent_upper (x z : ℝ) (hx : 0 < x) (hz : 0 < z) :
    Real.log x ≤ Real.log z + x / z - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hz)
  rw [Real.log_div hx.ne' hz.ne'] at h
  linarith

theorem norm_square_log_lower (q A D : ℝ)
    (hA : 0 < A) (hD : 0 < D) (hbound : A / D ≤ q ^ 2) :
    (Real.log A - Real.log D) / 2 ≤ Real.log q := by
  have h := Real.log_le_log (div_pos hA hD) hbound
  rw [Real.log_div hA.ne' hD.ne', Real.log_pow] at h
  norm_num at h
  linarith

def lowerDensity (w : J → ℝ → ℝ) (c d : J → ℝ) (z y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ((∑ i, w i y * (Real.log (c i) - d i / z)) - (Real.log z - 1))

theorem density_lower (w : J → ℝ) (c d : J → ℝ) (z f : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (hc : ∀ i, 0 < c i)
    (hz : 0 < z) (hD : 0 < ∑ i, w i * d i)
    (hmodel : (Real.log (∑ i, w i * c i) - Real.log (∑ i, w i * d i)) / 2 ≤ f) :
    (1 / 2 : ℝ) * ((∑ i, w i * (Real.log (c i) - d i / z)) - (Real.log z - 1)) ≤ f := by
  have hl := weighted_log_lower w c hw hs hc
  have hu := log_tangent_upper (∑ i, w i * d i) z hD hz
  have he : (∑ i, w i * (Real.log (c i) - d i / z)) =
      (∑ i, w i * Real.log (c i)) - (∑ i, w i * d i) / z := by
    simp only [mul_sub, mul_div_assoc, Finset.sum_sub_distrib, Finset.sum_div]
  rw [he]
  linarith

theorem integral_lower (w : J → ℝ → ℝ) (c d : J → ℝ) (z a b : ℝ)
    (f : ℝ → ℝ) (hab : a ≤ b) (hz : 0 < z) (hc : ∀ i, 0 < c i)
    (hwint : ∀ i, IntervalIntegrable (w i) volume a b)
    (hf : IntervalIntegrable f volume a b)
    (hw : ∀ y ∈ Ioo a b, ∀ i, 0 ≤ w i y)
    (hs : ∀ y ∈ Ioo a b, ∑ i, w i y = 1)
    (hD : ∀ y ∈ Ioo a b, 0 < ∑ i, w i y * d i)
    (hmodel : ∀ y ∈ Ioo a b,
      (Real.log (∑ i, w i y * c i) - Real.log (∑ i, w i y * d i)) / 2 ≤ f y) :
    (1 / 2 : ℝ) * ((∑ i, (∫ y : ℝ in a..b, w i y) *
      (Real.log (c i) - d i / z)) - (b - a) * (Real.log z - 1)) ≤
      ∫ y : ℝ in a..b, f y := by
  have hwc (i : J) : IntervalIntegrable
      (fun y => w i y * (Real.log (c i) - d i / z)) volume a b :=
    (hwint i).mul_const _
  have hsum : IntervalIntegrable
      (fun y => ∑ i, w i y * (Real.log (c i) - d i / z)) volume a b := by
    have he : (∑ i, (fun y : ℝ => w i y * (Real.log (c i) - d i / z))) =
        (fun y : ℝ => ∑ i, w i y * (Real.log (c i) - d i / z)) := by
      funext y
      simp only [Finset.sum_apply]
    rw [← he]
    exact IntervalIntegrable.sum Finset.univ (fun i _ => hwc i)
  have hg : IntervalIntegrable (lowerDensity w c d z) volume a b :=
    (hsum.sub intervalIntegrable_const).const_mul (1 / 2 : ℝ)
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hab hg hf
    (fun y hy => density_lower (fun i => w i y) c d z (f y)
      (hw y hy) (hs y hy) hc hz (hD y hy) (hmodel y hy))
  have he : (∫ y : ℝ in a..b, lowerDensity w c d z y) =
      (1 / 2 : ℝ) * ((∑ i, (∫ y : ℝ in a..b, w i y) *
        (Real.log (c i) - d i / z)) - (b - a) * (Real.log z - 1)) := by
    unfold lowerDensity
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hsum intervalIntegrable_const,
      intervalIntegral.integral_finsetSum (fun i _ => hwc i),
      intervalIntegral.integral_const]
    simp_rw [intervalIntegral.integral_mul_const]
    simp only [smul_eq_mul]
  rw [he] at hm
  exact hm

theorem polynomial_cell_log_lower (p : List ℚ) (a b : ℚ) (n : ℕ)
    (cs : Fin (n + 1) → ℚ) (hcheck : RationalPolynomialCell.accepts p a b n cs = true)
    (hcs : ∀ i, 0 < cs i) (hab : a < b) (y : ℝ)
    (hy : y ∈ Icc (a : ℝ) (b : ℝ)) :
    ∑ i, Bernstein.basis n i ((y-a)/(b-a)) * Real.log (cs i : ℝ) ≤
      Real.log (RationalComplexPolynomial.realEvaluator y (PolynomialPathMap.ofList p)) := by
  rw [RationalPolynomialCell.representation p a b n cs hcheck y hab]
  simpa only [mul_comm] using weighted_log_lower
    (fun i => Bernstein.basis n i ((y-a)/(b-a))) (fun i => (cs i : ℝ))
    (fun i => Bernstein.basis_nonneg n i _ (RationalPolynomialCell.cell_coordinate a b hab y hy))
    (Bernstein.basis_sum n _) (fun i => by exact_mod_cast hcs i)

#print axioms weighted_log_lower
#print axioms log_tangent_upper
#print axioms norm_square_log_lower
#print axioms density_lower
#print axioms integral_lower
#print axioms polynomial_cell_log_lower

end
end Gebendorfer.RadenkovicGutman.BernsteinLogIntegral
