/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFocus
namespace Gebendorfer.RadenkovicGutman.OriginHalfplane
open Focus
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A strict half-plane bound on the actual Schur disk, at every positive ordinate. -/
theorem linear_positive (d y : ℝ) (hd : 0 < d) (hy : 0 < y)
    (ζ : ℂ) (hζ : ‖ζ-g d y‖ ≤ r d y) :
    0 < y*(z y-ζ).re-2*(z y-ζ).im := by
  let w := z y-ζ
  have hr : 0 ≤ r d y := by unfold r; positivity
  have hn : Complex.normSq (ζ-g d y) ≤ (r d y)^2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) hr).mpr hζ
  have he : Complex.normSq (ζ-g d y)=
      (w.re-d)^2+(w.im+r d y)^2 := by
    dsimp [w,z,g,r]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
      Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      Complex.re_ofNat,Complex.im_ofNat]
    ring
  rw [he] at hn
  let t := y*w.re-2*w.im
  let u := y*d+2*r d y
  have hu : 0 < u := by dsimp [u,r]; positivity
  have hc : (t-u)^2+(2*(w.re-d)+y*(w.im+r d y))^2=
      (y^2+4)*((w.re-d)^2+(w.im+r d y)^2) := by
    dsimp [t,u]
    ring
  have hb := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ y^2+4)
  rw [← hc] at hb
  have hm : u^2-(y^2+4)*(r d y)^2=d^2*(y^2+7/4) := by
    dsimp [u,r]
    field_simp [hy.ne']
    ring
  have hmp : 0 < u^2-(y^2+4)*(r d y)^2 := by rw [hm]; positivity
  change 0 < t
  by_contra ht
  have htu : t*u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt ht) hu.le
  nlinarith [sq_nonneg t,sq_nonneg (2*(w.re-d)+y*(w.im+r d y))]

#print axioms linear_positive
end
end Gebendorfer.RadenkovicGutman.OriginHalfplane
