/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSymmetricTangentReserveIdentity
import Proofs.RadenkovicGutmanSymmetricConstantReserveIdentity

/-! The same original full reserves on both original ordinate strips. -/
namespace Gebendorfer.RadenkovicGutman.LowStripReserves
open Set
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem tangent_reserve (d y P Q c : ℝ) (hd : 46 ≤ d)
    (hP : y ≤ P) (hQ : y ≤ Q) (hc : c ∈ Ioc (0 : ℝ) (1/2))
    (hrelation : d*y=4*c/(1-c^2)) : 0 ≤ LowStripGeometry.reserve d y P Q c := by
  have hd0 : 0 < d := by linarith only [hd]
  have hh : 1/d ∈ Ioc (0 : ℝ) (1/46) := by
    refine ⟨by positivity,?_⟩
    apply (div_le_div_iff₀ hd0 (by norm_num : (0 : ℝ) < 46)).mpr
    linarith only [hd]
  have he : y=4*c*(1/d)/(1-c^2) := by
    calc
      y = (d*y)/d := by field_simp [hd0.ne']
      _ = (4*c/(1-c^2))/d := by rw [hrelation]
      _ = 4*c*(1/d)/(1-c^2) := by ring
  have h := SymmetricTangentReserveIdentity.original_inner_nonneg (1/d) c P Q hh hc
    (by rwa [← he]) (by rwa [← he])
  have hinv : 1/(1/d)=d := by field_simp [hd0.ne']
  rw [hinv,← he] at h
  exact LowStripReserveReduction.reserve_nonneg_of_inner d y P Q c h

theorem constant_reserve (d y P Q : ℝ) (hd : 46 ≤ d)
    (hy : y ∈ Icc (8/(3*d) : ℝ) (1/2)) (hP : y ≤ P) (hQ : y ≤ Q) :
    0 ≤ LowStripGeometry.reserve d y P Q 1 := by
  have hd0 : 0 < d := by linarith only [hd]
  have hcut : (0 : ℝ) < 8/(3*d) := by positivity
  have hy0 : 0 < y := lt_of_lt_of_le hcut hy.1
  have hprod := (div_le_iff₀ (by positivity : (0 : ℝ) < 3*d)).mp hy.1
  have hv : 0 ≤ d-8/(3*y) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3*y)).mpr
    nlinarith only [hprod]
  have h := SymmetricConstantReserveIdentity.original_inner_nonneg (d-8/(3*y)) y P Q hv
    ⟨hy0,hy.2⟩ hP hQ
  have he : 8/(3*y)+(d-8/(3*y))=d := by ring
  rw [he] at h
  exact LowStripReserveReduction.reserve_nonneg_of_inner d y P Q 1 h

#print axioms tangent_reserve
#print axioms constant_reserve
end
end Gebendorfer.RadenkovicGutman.LowStripReserves
