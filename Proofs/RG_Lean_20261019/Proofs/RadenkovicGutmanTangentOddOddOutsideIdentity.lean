/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanTangentOddOddOutside
import Proofs.RadenkovicGutmanLowStripGeometry

/-! Original positive clearing identity for the odd/odd tangent outside test.
Source: rg_multiarm_small_ordinate_lowstrip.py, parity_enclosure and
substitute_tangent_relation, at the original cutoff 46. -/
namespace Gebendorfer.RadenkovicGutman.TangentOddOddOutside
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

def ordinate (h c : ℝ) : ℝ := 4*c*h/(1-c^2)
def clearedForm (h c a b : ℝ) : ℝ :=
  h^2*c*(1-c^2)^10*LowStripGeometry.outside (1/h) (ordinate h c)
    (ordinate h c+a) (ordinate h c+b) c

theorem original_clearing_identity (h c a b : ℝ) (hh : h ≠ 0) (hc : c ≠ 0)
    (hd : 1-c^2 ≠ 0) :
    NestedHorner.eval (NestedInteger.castPoly 4 data) ![46*h,2*c,a,b] =
      (11765324404956231737802752 : ℝ)*clearedForm h c a b := by
  simp (maxSteps := 10000000) [data,NestedInteger.castPoly,NestedHorner.eval]
  dsimp only [clearedForm,ordinate,LowStripGeometry.outside,
    LowStripGeometry.lead,LowStripGeometry.bx,LowStripGeometry.bt,
    QuadraticDisk.outside,QuadraticDisk.gradientSq,Focus.A,Focus.B,
    Focus.N₀,Focus.D₀,Focus.z,Focus.g,Focus.r]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.re_ofNat,Complex.im_ofNat]
  field_simp [hh,hc,hd]
  ring

theorem original_outside_nonneg (h c a b : ℝ) (hh : h ∈ Ioc (0 : ℝ) (1/46))
    (hc : c ∈ Ioc (0 : ℝ) (1/2)) (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) :
    0 ≤ LowStripGeometry.outside (1/h) (ordinate h c)
      (ordinate h c+a) (ordinate h c+b) c := by
  have hd : 0 < 1-c^2 := by
    have hs := pow_le_pow_left₀ hc.1.le hc.2 2
    nlinarith only [hs]
  have hv : ∀ i : Fin 4, (![46*h,2*c,a,b] : Fin 4 → ℝ) i ∈ Icc (0 : ℝ) 1 := by
    intro i
    fin_cases i
    · change 46*h ∈ Icc (0 : ℝ) 1
      constructor <;> linarith [hh.1,hh.2]
    · change 2*c ∈ Icc (0 : ℝ) 1
      constructor <;> linarith [hc.1,hc.2]
    · exact ha
    · exact hb
  have h0 := unit_box_nonneg _ hv
  rw [original_clearing_identity h c a b hh.1.ne' hc.1.ne' hd.ne'] at h0
  have hf : 0 ≤ clearedForm h c a b := nonneg_of_mul_nonneg_right h0 (by norm_num)
  unfold clearedForm at hf
  exact nonneg_of_mul_nonneg_right hf
    (mul_pos (mul_pos (pow_pos hh.1 2) hc.1) (pow_pos hd 10))

#print axioms original_clearing_identity
#print axioms original_outside_nonneg
end
end Gebendorfer.RadenkovicGutman.TangentOddOddOutside
