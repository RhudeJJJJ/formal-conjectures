/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanEscapeDirectedCertificate
import Proofs.RadenkovicGutmanEscapeReserveCertificate
import Proofs.RadenkovicGutmanEscapeClearing
/-! Original actual graph escape bound; only the low-strip integral remains in strict fusion. -/
namespace Gebendorfer.RadenkovicGutman.HighDegreeEscape
open CorrelatedEscape Set
open scoped Classical
noncomputable section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
theorem signs (d : ℝ) (hd : 46 ≤ d) : Signs d := by
  exact signs_of_forms d hd EscapeDirectedCertificate.form_nonneg EscapeReserveCertificate.form_nonneg

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
