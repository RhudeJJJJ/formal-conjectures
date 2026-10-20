/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripGeometry

/-! Exact coverage of the original tangent coordinate s=4*c/(1-c^2).
Source: rg_multiarm_small_ordinate_lowstrip.py, substitute_tangent_relation. -/
namespace Gebendorfer.RadenkovicGutman.LowStripCoordinates
open Real Set
noncomputable section
set_option maxHeartbeats 0

theorem tangent_coordinate_exists (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) (8/3)) :
    ∃ c ∈ Ioc (0 : ℝ) (1/2), s=4*c/(1-c^2) := by
  let t := sqrt (s^2+4)
  have ht : 0 ≤ t := sqrt_nonneg _
  have htsq : t^2=s^2+4 := sq_sqrt (by positivity)
  have hp : 0 < 2+t := by positivity
  have hbound : 2*s ≤ 2+t := by
    by_cases h : s ≤ 1
    · linarith only [h,ht]
    · have h0 : 0 ≤ 2*s-2 := by linarith only [h]
      have hprod := mul_nonneg hs.1.le (show 0 ≤ 8-3*s by linarith only [hs.2])
      have hsq : (2*s-2)^2 ≤ t^2 := by nlinarith only [hprod,htsq]
      have hh := (sq_le_sq₀ h0 ht).mp hsq
      linarith only [hh]
  let c := s/(2+t)
  have hc0 : 0 < c := div_pos hs.1 hp
  have hcHalf : c ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ hp).mpr
    linarith only [hbound]
  have hcDen : 0 < 1-c^2 := by
    have h := pow_le_pow_left₀ hc0.le hcHalf 2
    nlinarith only [h]
  have he : (2+t)^2-s^2=4*(2+t) := by nlinarith only [htsq]
  have hcm : c*(2+t)=s := by dsimp [c]; field_simp [hp.ne']
  have hc2 := congrArg (fun x : ℝ => x^2) hcm
  simp only [mul_pow] at hc2
  have hz : (1-c^2)*(2+t)=4 := by
    apply (mul_right_cancel₀ hp.ne')
    nlinarith only [hc2,he]
  have hrel : s*(1-c^2)=4*c := by
    calc
      s*(1-c^2)=(c*(2+t))*(1-c^2) := by rw [hcm]
      _ = c*((1-c^2)*(2+t)) := by ring
      _ = c*4 := by rw [hz]
      _ = 4*c := by ring
  exact ⟨c,⟨hc0,hcHalf⟩,(eq_div_iff hcDen.ne').mpr hrel⟩

#print axioms tangent_coordinate_exists
end
end Gebendorfer.RadenkovicGutman.LowStripCoordinates
