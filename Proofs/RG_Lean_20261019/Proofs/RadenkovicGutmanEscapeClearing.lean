/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeDirectedIdentity
import Proofs.RadenkovicGutmanEscapeReserveIdentity
/-! Original positive clearing identities and assembly, under the two exact form signs. -/
namespace Gebendorfer.RadenkovicGutman.HighDegreeEscape
open CorrelatedEscape Set
open scoped Classical
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
theorem directed_clearing (d x a b : ℝ) (hd : 0 < d) (hx : 0 < x) :
    EscapeDirectedCertificate.form (1/d) x a b =
      -((1/d)^8*x^10*(1+x^2)^6)*
        directed d (d*x) (d*x+a/(d*x)) (d*x+b/(d*x)) (payment d x) := by
  have h1 : 1/(1/d)=d := by field_simp [hd.ne']
  have h2 : x/(1/d)=d*x := by field_simp [hd.ne'] <;> ring
  have h3 (a : ℝ) : a*(1/d)/x=a/(d*x) := by field_simp [hd.ne',hx.ne'] <;> ring
  unfold EscapeDirectedCertificate.form
  rw [h1,h2,h3 a,h3 b]
  ring

theorem reserve_clearing (d x a b : ℝ) (hd : 0 < d) (hx : 0 < x) :
    EscapeReserveCertificate.form (1/d) x a b =
      ((1/d)^16*x^16*(1+x^2)^12)*
        reserve d (d*x) (d*x+a/(d*x)) (d*x+b/(d*x)) (payment d x) := by
  have h1 : 1/(1/d)=d := by field_simp [hd.ne']
  have h2 : x/(1/d)=d*x := by field_simp [hd.ne'] <;> ring
  have h3 (a : ℝ) : a*(1/d)/x=a/(d*x) := by field_simp [hd.ne',hx.ne'] <;> ring
  unfold EscapeReserveCertificate.form
  rw [h1,h2,h3 a,h3 b]

theorem signs_of_forms (d : ℝ) (hd : 46 ≤ d)
    (hD0 : ∀ h x a b : ℝ, h ∈ Ioc (0 : ℝ) (1/46) → x ∈ Icc (653/2000 : ℝ) 10 →
      a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → 0 ≤ EscapeDirectedCertificate.form h x a b)
    (hR0 : ∀ h x a b : ℝ, h ∈ Ioc (0 : ℝ) (1/46) → x ∈ Icc (653/2000 : ℝ) 10 →
      a ∈ Icc (0 : ℝ) 1 → b ∈ Icc (0 : ℝ) 1 → 0 ≤ EscapeReserveCertificate.form h x a b) : Signs d := by
  have hd0 : 0 < d := by linarith only [hd]
  have hh : 1/d ∈ Ioc (0 : ℝ) (1/46) := by
    refine ⟨by positivity,?_⟩
    apply (div_le_div_iff₀ hd0 (by norm_num : (0 : ℝ) < 46)).mpr
    linarith only [hd]
  intro x hx a ha b hb
  have hx0 : 0 < x := by linarith only [hx.1]
  have hD := hD0 (1/d) x a b hh hx ha hb
  have hR := hR0 (1/d) x a b hh hx ha hb
  rw [directed_clearing d x a b hd0 hx0] at hD
  rw [reserve_clearing d x a b hd0 hx0] at hR
  constructor
  · have hp : 0 < (1/d)^8*x^10*(1+x^2)^6 := by positivity
    have hm : 0 ≤ ((1/d)^8*x^10*(1+x^2)^6)*
        (-directed d (d*x) (d*x+a/(d*x)) (d*x+b/(d*x)) (payment d x)) := by
      nlinarith only [hD]
    have hn := nonneg_of_mul_nonneg_right hm hp
    linarith only [hn]
  · exact nonneg_of_mul_nonneg_right hR (by positivity)

#print axioms directed_clearing
#print axioms reserve_clearing
#print axioms signs_of_forms
end
end Gebendorfer.RadenkovicGutman.HighDegreeEscape
