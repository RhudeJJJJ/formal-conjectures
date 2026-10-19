/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanLongArmGeometry1L
import Proofs.RadenkovicGutmanNestedHornerTransform
import Proofs.RadenkovicGutmanLongArmBothPolynomials
import Proofs.RadenkovicGutmanLongArmBothGeometry
import Proofs.RadenkovicGutmanBothLongD05
namespace Gebendorfer.RadenkovicGutman.LongArmBothFamily
open Focus CoreQuotient Set MeasureTheory
open scoped Classical
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
theorem coefficient_U05 (y v t : ℝ) (hy : 0 < y) : Complex.normSq (b 5 y (P y v) (Q y t) * star (e 5 y (P y v) (Q y t)) - a 5 (P y v) (Q y t) * star (c 5 y (P y v) (Q y t))) = scaleFactor y v t * up 5 y v t := by
  have hp : 0 < LongArmFamily1L.qDen y v := by unfold LongArmFamily1L.qDen; positivity
  have hq : 0 < LongArmFamily1L.qDen y t := by unfold LongArmFamily1L.qDen; positivity
  have hy0 : y ≠ 0 := hy.ne'
  rw [← BothLongD05.U_eval]
  unfold scaleFactor P Q LongArmFamily1L.Q LongArmFamily1L.qNum LongArmFamily1L.qDen b a c e A B N₀ D₀ g z
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat, Complex.star_def, Complex.conj_re, Complex.conj_im]
  simp [BothLongD05.U, NestedHorner.eval]
  field_simp
  ring
#print axioms coefficient_U05
end
end Gebendorfer.RadenkovicGutman.LongArmBothFamily
