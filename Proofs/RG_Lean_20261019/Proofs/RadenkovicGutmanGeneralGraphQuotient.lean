/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanRootSchur
import Proofs.RadenkovicGutmanActualFusionIntegral

namespace Gebendorfer.RadenkovicGutman.GeneralGraphQuotient
open CoreQuotient PathRecurrence
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def point (x y : ℝ) : ℂ := x+(y : ℂ)*Complex.I
def center (x y d : ℝ) : ℂ := (x-d : ℝ)+(y+d/(2*y) : ℝ)*Complex.I

def numeratorCoefficient (z : ℂ) (p q : ℕ) : ℂ :=
  (den z (p+1)-num z (p+1))*(den z (q+1)-num z (q+1))
def sourceConstant (z : ℂ) (p q : ℕ) : ℂ :=
  2*den z (p+1)*den z (q+1)-num z (p+1)*den z (q+1)-num z (q+1)*den z (p+1)
def denominatorCoefficient (z : ℂ) (p q : ℕ) : ℂ :=
  den z (p+q+2)-num z (p+q+2)
def fusedConstant (z : ℂ) (p q : ℕ) : ℂ := den z (p+q+2)
def quotient (z : ℂ) (p q : ℕ) (s : ℂ) : ℂ :=
  (numeratorCoefficient z p q*s-sourceConstant z p q)/
    (denominatorCoefficient z p q*s-fusedConstant z p q)

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem schur_nonzero (C : SimpleGraph V) (u : V) (z : ℂ) (hz : 0 < z.im) :
    RootSchur.schurScalar C u z ≠ 0 := by
  have hi := (RootSchur.graph_schur_disk C u z hz).2
  intro hs
  rw [hs] at hi
  change z.im ≤ 0 at hi
  linarith

/-- Polynomial path factors at arbitrary real shifts, bound to the actual
source/fused Laplacian determinants with their orientation retained. -/
theorem actual_quotient (C : SimpleGraph V) (u : V) (z : ℂ) (hz : 0 < z.im)
    (p q : ℕ) :
    (shifted z (source C u p q)).det/(shifted z (fused C u p q)).det=
      quotient z p q (RootSchur.schurScalar C u z) := by
  let s := RootSchur.schurScalar C u z
  have hs : s ≠ 0 := schur_nonzero C u z hz
  have hc : (shifted z C).det ≠ 0 := (shifted_isUnit z hz.ne' C).ne_zero
  have hf : denominatorCoefficient z p q-s⁻¹*fusedConstant z p q ≠ 0 := by
    have hh := (shifted_isUnit z hz.ne' (fused C u p q)).ne_zero
    rw [fused_det z hz.ne',RootSchur.root_resolvent_schur C u z hz] at hh
    exact (mul_ne_zero_iff.mp hh).2
  have he : denominatorCoefficient z p q-s⁻¹*fusedConstant z p q=
      (denominatorCoefficient z p q*s-fusedConstant z p q)/s := by
    field_simp [hs]
    all_goals ring
  have hden : denominatorCoefficient z p q*s-fusedConstant z p q ≠ 0 := by
    intro hzero
    apply hf
    rw [he,hzero,zero_div]
  rw [source_det z hz.ne',fused_det z hz.ne',RootSchur.root_resolvent_schur C u z hz]
  change ((shifted z C).det*(numeratorCoefficient z p q-s⁻¹*sourceConstant z p q))/
      ((shifted z C).det*(denominatorCoefficient z p q-s⁻¹*fusedConstant z p q))=
    (numeratorCoefficient z p q*s-sourceConstant z p q)/
      (denominatorCoefficient z p q*s-fusedConstant z p q)
  field_simp [hc,hs,hf,hden]
  all_goals ring

theorem actual_disk (C : SimpleGraph V) (u : V) (x y : ℝ) (hy : 0 < y) :
    ‖RootSchur.schurScalar C u (point x y)-center x y (C.degree u)‖ ≤
      (C.degree u : ℝ)/(2*y) := by
  have hz : 0 < (point x y).im := by simpa [point] using hy
  have h := (RootSchur.graph_schur_disk C u (point x y) hz).1
  have him : (point x y).im=y := by simp [point]
  have he : point x y-(C.degree u : ℂ)+
      ((C.degree u : ℝ)/(2*y) : ℝ)*Complex.I=center x y (C.degree u) := by
    unfold point center
    push_cast
    ring
  rw [him,he] at h
  exact h

theorem actual_logarithm (C : SimpleGraph V) (u : V) (p q : ℕ)
    (x y : ℝ) (hy : 0 < y) :
    MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) x y=
      Real.log ‖quotient (point x y) p q (RootSchur.schurScalar C u (point x y))‖ := by
  change Real.log ‖(shifted (point x y) (source C u p q)).det/
    (shifted (point x y) (fused C u p q)).det‖=_
  rw [actual_quotient C u (point x y) (by simpa [point] using hy) p q]

#print axioms schur_nonzero
#print axioms actual_quotient
#print axioms actual_disk
#print axioms actual_logarithm
end
end Gebendorfer.RadenkovicGutman.GeneralGraphQuotient
