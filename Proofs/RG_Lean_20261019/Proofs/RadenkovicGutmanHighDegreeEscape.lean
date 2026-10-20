/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeDirectedCertificate
import Proofs.RadenkovicGutmanEscapeReserveCertificate

/-! Original degree-46 correlated escape bound and actual graph specialization.
The smaller-ordinate integral remains a separate hypothesis. -/
namespace Gebendorfer.RadenkovicGutman.HighDegreeEscape
open CorrelatedEscape Set
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

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

theorem signs (d : ℝ) (hd : 46 ≤ d) : Signs d := by
  have hd0 : 0 < d := by linarith only [hd]
  have hh : 1/d ∈ Ioc (0 : ℝ) (1/46) := by
    refine ⟨by positivity,?_⟩
    apply (div_le_div_iff₀ hd0 (by norm_num : (0 : ℝ) < 46)).mpr
    linarith only [hd]
  intro x hx a ha b hb
  have hx0 : 0 < x := by linarith only [hx.1]
  have hD := EscapeDirectedCertificate.form_nonneg (1/d) x a b hh hx ha hb
  have hR := EscapeReserveCertificate.form_nonneg (1/d) x a b hh hx ha hb
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

attribute [-instance] SimpleGraph.fintypeEdgeSetSup
open CoreQuotient

theorem graph_lower {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : 46 ≤ C.degree u) (y : ℝ)
    (hy : y ∈ Icc ((653/2000 : ℝ)*(C.degree u : ℝ)) (10*(C.degree u : ℝ))) :
    TailIntegral.escapeDensity (C.degree u) y ≤
      MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y := by
  exact graph_lower_of_signs C u p q hd (signs _ (by exact_mod_cast hd)) y hy

theorem strict_fusion_of_lowstrip {m : ℕ} (C : SimpleGraph (Fin m))
    (u : Fin m) (p q : ℕ) (hT : (source C u p q).IsTree) (hd : 46 ≤ C.degree u)
    (hlow : (-(8/3 : ℝ)*Real.log 2-2*Real.log 3)/(C.degree u : ℝ)-Real.log 2/2 ≤
      ∫ y : ℝ in (0 : ℝ)..(1/2), MixedGraphIntegral.logarithm (source C u p q) (fused C u p q) 2 y) :
    laplacianEnergy (fused C u p q) < laplacianEnergy (source C u p q) := by
  exact HighDegreeTail.strict_fusion_of_lowstrip_escape C u p q hT hd hlow
    (graph_lower C u p q hd)

#print axioms directed_clearing
#print axioms reserve_clearing
#print axioms signs
#print axioms graph_lower
#print axioms strict_fusion_of_lowstrip
attribute [instance] SimpleGraph.fintypeEdgeSetSup
end
end Gebendorfer.RadenkovicGutman.HighDegreeEscape
