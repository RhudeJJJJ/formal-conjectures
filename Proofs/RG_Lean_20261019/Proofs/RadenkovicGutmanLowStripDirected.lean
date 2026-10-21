/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripOutside
import Proofs.RadenkovicGutmanCorrelatedEscapeReduction

/-! Original convex low-strip directed condition for every physical arm pair.
Source: original Focus coefficients and low/constant-strip disk conditions.
The complete reserve square remains a separate obligation. -/
namespace Gebendorfer.RadenkovicGutman.LowStripDirected
open Set LowStripGeometry
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def anNegative (y P Q : ℝ) : ℝ := 4+2*(P^2+Q^2)+y*(P+Q)*(P*Q+1)
def bdNegative (y P Q : ℝ) : ℝ := (P+Q-y)*(y*(P*Q-1)+2*(P+Q))

theorem bx_identity (y P Q c : ℝ) :
    bx y P Q c = -2*(anNegative y P Q-(c^2/4)*bdNegative y P Q) := by
  simp only [bx,anNegative,bdNegative,Focus.A,Focus.B,Focus.N₀,Focus.D₀,Focus.z,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem quarter_difference_identity (y P Q : ℝ) :
    anNegative y P Q-bdNegative y P Q/4 =
      4+(3/2 : ℝ)*(P-Q)^2+2*(P*Q)+(3/4 : ℝ)*y*(P+Q)*(P*Q)+
        (7/4 : ℝ)*y*(P+Q-2*y)+(13/4 : ℝ)*y^2+(1/4 : ℝ)*y^2*(P*Q) := by
  dsimp [anNegative,bdNegative]
  ring

theorem bx_nonpos (y P Q c : ℝ) (hy : 0 < y) (hP : y ≤ P) (hQ : y ≤ Q)
    (hc : c ∈ Icc (0 : ℝ) 1) : bx y P Q c ≤ 0 := by
  have hP0 : 0 ≤ P := le_trans hy.le hP
  have hQ0 : 0 ≤ Q := le_trans hy.le hQ
  have hpq : 0 ≤ P*Q := mul_nonneg hP0 hQ0
  have hgap : 0 ≤ P+Q-2*y := by linarith only [hP,hQ]
  have hbracket : 0 ≤ y*(P*Q-1)+2*(P+Q) := by
    have h := mul_nonneg hy.le hpq
    nlinarith only [h,hP,hQ,hy]
  have hbd : 0 ≤ bdNegative y P Q := by
    unfold bdNegative
    exact mul_nonneg (by linarith only [hP,hQ,hy]) hbracket
  have hquarter : 0 ≤ anNegative y P Q-bdNegative y P Q/4 := by
    rw [quarter_difference_identity]
    positivity
  have hc2 := pow_le_pow_left₀ hc.1 hc.2 2
  have hk : 0 ≤ 1/4-c^2/4 := by nlinarith only [hc2]
  have hdiff : 0 ≤ anNegative y P Q-(c^2/4)*bdNegative y P Q := by
    calc
      0 ≤ (anNegative y P Q-bdNegative y P Q/4)+(1/4-c^2/4)*bdNegative y P Q :=
        add_nonneg hquarter (mul_nonneg hk hbd)
      _ = anNegative y P Q-(c^2/4)*bdNegative y P Q := by ring
  rw [bx_identity]
  nlinarith only [hdiff]

theorem anchor_identity (y P Q c : ℝ) :
    CorrelatedEscapeReduction.baseValue (lead y P Q c) (bx y P Q c)
      (bt y P Q c) (constant y P Q c) y =
        (1-c^2/4)*(4+y^2)*(P*Q+1)^2 := by
  simp only [CorrelatedEscapeReduction.baseValue,QuadraticDisk.value,lead,bx,bt,constant,
    Focus.A,Focus.B,Focus.N₀,Focus.D₀,Focus.z,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem directed_nonneg_of_lead (d y P Q c : ℝ) (hd : 4 ≤ d) (hy : 0 < y)
    (hP : y ≤ P) (hQ : y ≤ Q) (hc : c ∈ Icc (0 : ℝ) 1)
    (ha : 0 ≤ lead y P Q c) : 0 ≤ directed d y P Q c := by
  have hd0 : 0 ≤ d := by linarith only [hd]
  have hP0 : 0 ≤ P := le_trans hy.le hP
  have hQ0 : 0 ≤ Q := le_trans hy.le hQ
  have hpq : 0 ≤ P*Q := mul_nonneg hP0 hQ0
  have hc2 := pow_le_pow_left₀ hc.1 hc.2 2
  have hk : 0 ≤ 1-c^2/4 := by nlinarith only [hc2]
  have hanchor : 0 ≤ CorrelatedEscapeReduction.baseValue (lead y P Q c)
      (bx y P Q c) (bt y P Q c) (constant y P Q c) y := by
    rw [anchor_identity]
    positivity
  have hbx := bx_nonpos y P Q c hy hP hQ hc
  have hcore : 0 ≤ CorrelatedEscapeReduction.coreValue (lead y P Q c)
      (bx y P Q c) (bt y P Q c) (constant y P Q c) d y := by
    have hA := mul_nonneg (mul_nonneg ha hd0) (sub_nonneg.mpr hd)
    have hB := mul_nonneg hd0 (neg_nonneg.mpr hbx)
    unfold CorrelatedEscapeReduction.coreValue CorrelatedEscapeReduction.horizontal
    nlinarith only [hanchor,hA,hB]
  have hdelta : 0 ≤ CorrelatedEscapeReduction.vertical (lead y P Q c) (bt y P Q c) y := by
    unfold CorrelatedEscapeReduction.vertical
    rw [LowStripOutside.vertical_offset_identity]
    have hbracket : 0 ≤ y*(P*Q-1)+2*(P+Q) := by
      have h := mul_nonneg hy.le hpq
      nlinarith only [h,hP,hQ,hy]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hk) (by linarith only [hpq])) hbracket
  have hr : 0 ≤ Focus.r d y := by unfold Focus.r; positivity
  unfold directed
  change 0 ≤ QuadraticDisk.directed _ _ _ _ _
    (CorrelatedEscapeReduction.center d y (Focus.r d y))
  rw [CorrelatedEscapeReduction.directed_translation]
  exact mul_nonneg (mul_nonneg (by norm_num) ha)
    (add_nonneg (add_nonneg hcore (mul_nonneg hr hdelta)) (by positivity))

attribute [-instance] SimpleGraph.fintypeEdgeSetSup
theorem actual_tangent_directed {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 4 ≤ C.degree u) (y c : ℝ)
    (hy : 0 < y) (hc : c ∈ Icc (0 : ℝ) (1/2)) :
    0 ≤ directed (C.degree u) y
      (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) c := by
  have hp : y ≤ y+PathEnclosure.arm y p/y :=
    le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y p) hy.le)
  have hq : y ≤ y+PathEnclosure.arm y q/y :=
    le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y q) hy.le)
  exact directed_nonneg_of_lead _ _ _ _ _ (by exact_mod_cast hd) hy hp hq
    ⟨hc.1,le_trans hc.2 (by norm_num)⟩
    (TailHalfGeometry.tangent_lead_pos _ _ _ _ hy hp hq hc).le

theorem actual_constant_directed {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 4 ≤ C.degree u) (y : ℝ) (hy : 0 < y) :
    0 ≤ directed (C.degree u) y
      (y+PathEnclosure.arm y p/y) (y+PathEnclosure.arm y q/y) 1 := by
  have hp : y ≤ y+PathEnclosure.arm y p/y :=
    le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y p) hy.le)
  have hq : y ≤ y+PathEnclosure.arm y q/y :=
    le_add_of_nonneg_right (div_nonneg (PathEnclosure.arm_nonneg y q) hy.le)
  exact directed_nonneg_of_lead _ _ _ _ _ (by exact_mod_cast hd) hy hp hq (by norm_num)
    (LowStripConstantGeometry.lead_pos _ _ _ hy hp hq).le

#print axioms bx_identity
#print axioms quarter_difference_identity
#print axioms bx_nonpos
#print axioms anchor_identity
#print axioms directed_nonneg_of_lead
#print axioms actual_tangent_directed
#print axioms actual_constant_directed
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.LowStripDirected
