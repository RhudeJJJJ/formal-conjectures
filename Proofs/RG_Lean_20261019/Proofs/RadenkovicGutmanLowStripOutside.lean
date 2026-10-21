/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripConstantGeometry

/-! Analytic discharge of the original low-strip outside condition.
Source: the exact original A,B,N0,D0 coefficients in Focus and the original
outside test in rg_multiarm_small_ordinate_lowstrip.py. The directed and
complete reserve conditions remain separate obligations. -/
namespace Gebendorfer.RadenkovicGutman.LowStripOutside
open Set LowStripGeometry
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

theorem vertical_offset_identity (y P Q c : ℝ) :
    2*lead y P Q c*y+bt y P Q c =
      2*(1-c^2/4)*(P*Q+1)*(y*(P*Q-1)+2*(P+Q)) := by
  simp only [lead,bt,Focus.A,Focus.B,Focus.N₀,Focus.D₀,Focus.z,
    Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem outside_nonneg_of_lead (d y P Q c : ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) (hc : c ∈ Icc (0 : ℝ) 1)
    (ha : 0 ≤ lead y P Q c) : 0 ≤ outside d y P Q c := by
  have hP0 : 0 ≤ P := le_trans hy.le hP
  have hQ0 : 0 ≤ Q := le_trans hy.le hQ
  have hpq : 0 ≤ P*Q := mul_nonneg hP0 hQ0
  have hbracket : 0 ≤ y*(P*Q-1)+2*(P+Q) := by
    have h := mul_nonneg hy.le hpq
    nlinarith only [h,hP,hQ,hy]
  have hc2 := pow_le_pow_left₀ hc.1 hc.2 2
  have hk : 0 ≤ 1-c^2/4 := by nlinarith only [hc2]
  let delta := 2*lead y P Q c*y+bt y P Q c
  have hdelta : 0 ≤ delta := by
    dsimp only [delta]
    rw [vertical_offset_identity]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk) (by linarith only [hpq])) hbracket
  have hr : 0 ≤ Focus.r d y := by unfold Focus.r; positivity
  have hbase : 0 ≤ 2*lead y P Q c*Focus.r d y := by positivity
  have hg : (Focus.g d y).im=y+Focus.r d y := by
    simp only [Focus.g,Focus.r,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_add,add_zero]
  have he : 2*lead y P Q c*(Focus.g d y).im+bt y P Q c =
      2*lead y P Q c*Focus.r d y+delta := by rw [hg]; dsimp only [delta]; ring
  unfold outside QuadraticDisk.outside QuadraticDisk.gradientSq
  rw [he]
  nlinarith only [sq_nonneg (2*lead y P Q c*(Focus.g d y).re+bx y P Q c),
    sq_nonneg delta,mul_nonneg hbase hdelta]

theorem tangent_outside_nonneg (d y P Q c : ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) (hc : c ∈ Icc (0 : ℝ) (1/2)) :
    0 ≤ outside d y P Q c :=
  outside_nonneg_of_lead d y P Q c hd hy hP hQ
    ⟨hc.1,le_trans hc.2 (by norm_num)⟩
    (TailHalfGeometry.tangent_lead_pos y P Q c hy hP hQ hc).le

theorem constant_outside_nonneg (d y P Q : ℝ) (hd : 0 ≤ d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) : 0 ≤ outside d y P Q 1 :=
  outside_nonneg_of_lead d y P Q 1 hd hy hP hQ (by norm_num)
    (LowStripConstantGeometry.lead_pos y P Q hy hP hQ).le

attribute [-instance] SimpleGraph.fintypeEdgeSetSup
theorem actual_tangent_outside {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (y c : ℝ) (hy : 0 < y)
    (hc : c ∈ Icc (0 : ℝ) (1/2)) :
    0 ≤ outside (C.degree u) y
      (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c := by
  apply tangent_outside_nonneg _ _ _ _ _ (by positivity) hy
  · exact le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y p) hy.le)
  · exact le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y q) hy.le)
  · exact hc

theorem actual_constant_outside {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (y : ℝ) (hy : 0 < y) :
    0 ≤ outside (C.degree u) y
      (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) 1 := by
  apply constant_outside_nonneg _ _ _ _ (by positivity) hy
  · exact le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y p) hy.le)
  · exact le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y q) hy.le)

#print axioms vertical_offset_identity
#print axioms outside_nonneg_of_lead
#print axioms tangent_outside_nonneg
#print axioms constant_outside_nonneg
#print axioms actual_tangent_outside
#print axioms actual_constant_outside
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.LowStripOutside
