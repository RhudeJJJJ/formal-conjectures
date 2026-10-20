/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeDirectedData
import Proofs.RadenkovicGutmanCorrelatedEscape

/-! Exact original positively cleared polynomial identity; signs are separate. -/
namespace Gebendorfer.RadenkovicGutman.EscapeDirectedCertificate
open Set
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
abbrev data := EscapeDirectedData.data
abbrev degrees := EscapeDirectedData.degrees

def form (h x a b : ℝ) : ℝ := -h^8*x^10*(1+x^2)^6*CorrelatedEscape.directed (1/h) (x/h) (x/h+a*h/x) (x/h+b*h/x) (CorrelatedEscape.payment (1/h) x)

theorem data_identity (H U a b : ℝ) (hH : H ≠ 0)
    (hX : (653/2000 : ℝ)+(19347/2000 : ℝ)*U ≠ 0) :
    NestedHorner.eval (NestedInteger.castPoly 4 data) ![H,U,a,b] =
      (9519459831916749656232983908361175040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)*form (H/46) ((653/2000)+(19347/2000)*U) a b := by
  simp [data,EscapeDirectedData.data,NestedInteger.castPoly,NestedHorner.eval]
  dsimp only [form,
    CorrelatedEscape.directed,CorrelatedEscape.reserve,CorrelatedEscape.lead,
    CorrelatedEscape.bx,CorrelatedEscape.bt,CorrelatedEscape.constant,
    CorrelatedEscape.payment,CorrelatedEscape.cubic,CorrelatedEscape.quadratic,
    QuadraticDisk.directed,QuadraticDisk.reserve,QuadraticDisk.gradientSq,
    Focus.A,Focus.B,Focus.N₀,Focus.D₀,Focus.z,Focus.g,Focus.r]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,Complex.re_ofNat,Complex.im_ofNat]
  field_simp [hH,hX,show (1+((653/2000 : ℝ)+(19347/2000 : ℝ)*U)^2) ≠ 0 by positivity]
  ring

#print axioms data_identity
end
end Gebendorfer.RadenkovicGutman.EscapeDirectedCertificate
