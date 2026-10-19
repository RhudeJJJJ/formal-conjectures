/-
Copyright 2026 Jonas J. Gebendorfer. Apache 2.0.
Linear-fractional disk enclosure and its rationalized distance bound.
Source: Gebendorfer, Laplacian energy of trees and pendant-path fusion,
5 September 2026, Section 4.
-/
import Proofs.RadenkovicGutmanReciprocalDisk

namespace Gebendorfer.RadenkovicGutman.MobiusDisk

open Complex

theorem numerator_identity (a b c d η : ℂ) :
    ((Complex.normSq d - Complex.normSq c : ℝ) : ℂ) * (a * η + b) -
      (b * star d - a * star c) * (c * η + d) =
      (a * d - b * c) * (star c + star d * η) := by
  have hc : (Complex.normSq c : ℂ) = c * star c := by
    simpa only [Complex.star_def] using (Complex.mul_conj c).symm
  have hd : (Complex.normSq d : ℂ) = d * star d := by
    simpa only [Complex.star_def] using (Complex.mul_conj d).symm
  push_cast
  rw [hc, hd]
  ring

theorem circle_identity (c d η : ℂ) :
    Complex.normSq (c * η + d) - Complex.normSq (star c + star d * η) =
      (Complex.normSq d - Complex.normSq c) * (1 - Complex.normSq η) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem denominator_ne_zero (c d η : ℂ)
    (hE : 0 < Complex.normSq d - Complex.normSq c) (hη : ‖η‖ ≤ 1) :
    c * η + d ≠ 0 := by
  have hnorm : ‖c‖ < ‖d‖ := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hE
    nlinarith [norm_nonneg c, norm_nonneg d]
  intro he
  have hd : d = -(c * η) := by linear_combination he
  have hm := mul_le_mul_of_nonneg_left hη (norm_nonneg c)
  rw [hd, norm_neg, norm_mul] at hnorm
  nlinarith

/-- The disk image enclosure, without assuming a minimum formula. -/
theorem image_disk (a b c d η : ℂ)
    (hE : 0 < Complex.normSq d - Complex.normSq c) (hη : ‖η‖ ≤ 1) :
    ‖(a * η + b) / (c * η + d) -
        (b * star d - a * star c) / (Complex.normSq d - Complex.normSq c : ℝ)‖ ≤
      ‖a * d - b * c‖ / (Complex.normSq d - Complex.normSq c) := by
  let E := Complex.normSq d - Complex.normSq c
  have hE0 : (E : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hE.ne'
  have hden := denominator_ne_zero c d η hE hη
  have hη2 : Complex.normSq η ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg η]
  have hcircle : ‖star c + star d * η‖ ≤ ‖c * η + d‖ := by
    have h := circle_identity c d η
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
    have hp := mul_nonneg hE.le (sub_nonneg.mpr hη2)
    nlinarith [norm_nonneg (star c + star d * η), norm_nonneg (c * η + d)]
  have hid : (a * η + b) / (c * η + d) - (b * star d - a * star c) / (E : ℂ) =
      ((a * d - b * c) * ((star c + star d * η) / (c * η + d))) / (E : ℂ) := by
    apply (eq_div_iff hE0).mpr
    rw [sub_mul, div_mul_cancel₀ _ hE0, ← mul_div_assoc]
    apply (eq_div_iff hden).mpr
    rw [sub_mul, mul_right_comm _ (E : ℂ), div_mul_cancel₀ _ hden]
    convert numerator_identity a b c d η using 1; ring
  rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE,
    norm_mul, norm_div]
  apply div_le_div_of_nonneg_right _ hE.le
  calc
    ‖a * d - b * c‖ * (‖star c + star d * η‖ / ‖c * η + d‖) ≤
        ‖a * d - b * c‖ * 1 :=
      mul_le_mul_of_nonneg_left ((div_le_one (norm_pos_iff.mpr hden)).mpr hcircle)
        (norm_nonneg _)
    _ = _ := mul_one _

theorem center_distance_identity (a b c d : ℂ) :
    ‖b * star d - a * star c‖ ^ 2 - ‖a * d - b * c‖ ^ 2 =
      (Complex.normSq d - Complex.normSq c) *
        (Complex.normSq b - Complex.normSq a) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The rationalized distance from zero; this is the lower bound used by certificates. -/
theorem rationalized_lower_bound (a b c d η : ℂ)
    (hE : 0 < Complex.normSq d - Complex.normSq c)
    (hN : 0 < Complex.normSq b - Complex.normSq a) (hη : ‖η‖ ≤ 1) :
    (Complex.normSq b - Complex.normSq a) /
      (‖b * star d - a * star c‖ + ‖a * d - b * c‖) ≤
      ‖(a * η + b) / (c * η + d)‖ := by
  let E := Complex.normSq d - Complex.normSq c
  let N := Complex.normSq b - Complex.normSq a
  let C := b * star d - a * star c
  let D := a * d - b * c
  let f := (a * η + b) / (c * η + d)
  have hid : ‖C‖ ^ 2 - ‖D‖ ^ 2 = E * N := center_distance_identity a b c d
  have hsep : ‖D‖ < ‖C‖ := by
    have hp := mul_pos hE hN
    nlinarith [norm_nonneg C, norm_nonneg D]
  have hsum : 0 < ‖C‖ + ‖D‖ := by linarith [norm_nonneg D]
  have h := image_disk a b c d η hE hη
  change ‖f - C / (E : ℂ)‖ ≤ ‖D‖ / E at h
  have ht := norm_sub_norm_le (C / (E : ℂ)) f
  rw [norm_sub_rev] at ht
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE] at ht
  change ‖C‖ / E - ‖f‖ ≤ ‖f - C / (E : ℂ)‖ at ht
  have hbound : ‖C‖ - ‖D‖ ≤ E * ‖f‖ := by
    have hh : (‖C‖ - ‖D‖) / E ≤ ‖f‖ := by rw [sub_div]; linarith
    simpa only [mul_comm] using (div_le_iff₀ hE).mp hh
  have heq : N / (‖C‖ + ‖D‖) = (‖C‖ - ‖D‖) / E := by
    apply (div_eq_div_iff hsum.ne' hE.ne').mpr
    nlinarith [hid]
  change N / (‖C‖ + ‖D‖) ≤ ‖f‖
  rw [heq]
  exact (div_le_iff₀ hE).mpr (by simpa only [mul_comm] using hbound)

#print axioms image_disk
#print axioms rationalized_lower_bound

end Gebendorfer.RadenkovicGutman.MobiusDisk
