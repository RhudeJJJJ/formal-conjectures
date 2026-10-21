/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLowStripDirected

/-! Exact reduction of the same full convex reserve, before sign checking. -/
namespace Gebendorfer.RadenkovicGutman.LowStripReserveReduction
open LowStripGeometry
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def a (y P Q c : ℝ) : ℝ :=
  (1-c^2/4)*(1+P^2)*(1+Q^2)-(c^2/4)*(2*P-y)*(2*Q-y)
def b (y P Q c : ℝ) : ℝ :=
  -2*(LowStripDirected.anNegative y P Q-(c^2/4)*LowStripDirected.bdNegative y P Q)
def anchor (y P Q c : ℝ) : ℝ := (1-c^2/4)*(4+y^2)*(P*Q+1)^2
def delta (y P Q c : ℝ) : ℝ :=
  2*(1-c^2/4)*(P*Q+1)*(y*(P*Q-1)+2*(P+Q))
def horizontal (y P Q c : ℝ) : ℝ := 4*a y P Q c+b y P Q c
def core (d y P Q c : ℝ) : ℝ := anchor y P Q c+a y P Q c*d^2-d*horizontal y P Q c
def inner (d y P Q c : ℝ) : ℝ :=
  (core d y P Q c)^2+2*core d y P Q c*(d/(2*y))*delta y P Q c+
    (d/(2*y))^2*(4*a y P Q c*anchor y P Q c-(horizontal y P Q c)^2)

theorem lead_identity (y P Q c : ℝ) : lead y P Q c = a y P Q c := by
  simp only [lead,a,Focus.A,Focus.B,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem reserve_identity (d y P Q c : ℝ) :
    reserve d y P Q c = 16*(a y P Q c)^2*inner d y P Q c := by
  unfold reserve
  change QuadraticDisk.reserve _ _ _ _ _
    (CorrelatedEscapeReduction.center d y (Focus.r d y)) = _
  rw [CorrelatedEscapeReduction.reserve_translation]
  simp only [CorrelatedEscapeReduction.coreValue,CorrelatedEscapeReduction.horizontal,
    CorrelatedEscapeReduction.vertical]
  simp only [LowStripDirected.anchor_identity,LowStripOutside.vertical_offset_identity]
  simp only [LowStripDirected.bx_identity,lead_identity]
  rfl

theorem reserve_nonneg_of_inner (d y P Q c : ℝ) (h : 0 ≤ inner d y P Q c) :
    0 ≤ reserve d y P Q c := by
  rw [reserve_identity]
  positivity

#print axioms lead_identity
#print axioms reserve_identity
#print axioms reserve_nonneg_of_inner
end
end Gebendorfer.RadenkovicGutman.LowStripReserveReduction
