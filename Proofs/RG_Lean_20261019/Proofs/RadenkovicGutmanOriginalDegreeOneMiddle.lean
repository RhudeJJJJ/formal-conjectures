/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorCoverageComplete
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteAllCertificates
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch00
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch01
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch02
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch03
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch04
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch05
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch06
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch07
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch08
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch09
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch10
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch11
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch12
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch13
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch14
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch15
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch16
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch17
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch18
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch19
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch20
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch21
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch22
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch23
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch24
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch25
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch26
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch27
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch28
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch29
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch30
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch31
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch32
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch33
namespace Gebendorfer.RadenkovicGutman.OriginalDegreeOneMiddle
open CoreQuotient ActualFusionIntegral OriginalAssembly DegreeOneMiddleAnchors
open MiddleOriginalAnchorPredicate
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def certificateAnchors : List Anchor := MiddleOriginalAnchorCertificateBatch00.anchors ++ MiddleOriginalAnchorCertificateBatch01.anchors ++ MiddleOriginalAnchorCertificateBatch02.anchors ++ MiddleOriginalAnchorCertificateBatch03.anchors ++ MiddleOriginalAnchorCertificateBatch04.anchors ++ MiddleOriginalAnchorCertificateBatch05.anchors ++ MiddleOriginalAnchorCertificateBatch06.anchors ++ MiddleOriginalAnchorCertificateBatch07.anchors ++ MiddleOriginalAnchorCertificateBatch08.anchors ++ MiddleOriginalAnchorCertificateBatch09.anchors ++ MiddleOriginalAnchorCertificateBatch10.anchors ++ MiddleOriginalAnchorCertificateBatch11.anchors ++ MiddleOriginalAnchorCertificateBatch12.anchors ++ MiddleOriginalAnchorCertificateBatch13.anchors ++ MiddleOriginalAnchorCertificateBatch14.anchors ++ MiddleOriginalAnchorCertificateBatch15.anchors ++ MiddleOriginalAnchorCertificateBatch16.anchors ++ MiddleOriginalAnchorCertificateBatch17.anchors ++ MiddleOriginalAnchorCertificateBatch18.anchors ++ MiddleOriginalAnchorCertificateBatch19.anchors ++ MiddleOriginalAnchorCertificateBatch20.anchors ++ MiddleOriginalAnchorCertificateBatch21.anchors ++ MiddleOriginalAnchorCertificateBatch22.anchors ++ MiddleOriginalAnchorCertificateBatch23.anchors ++ MiddleOriginalAnchorCertificateBatch24.anchors ++ MiddleOriginalAnchorCertificateBatch25.anchors ++ MiddleOriginalAnchorCertificateBatch26.anchors ++ MiddleOriginalAnchorCertificateBatch27.anchors ++ MiddleOriginalAnchorCertificateBatch28.anchors ++ MiddleOriginalAnchorCertificateBatch29.anchors ++ MiddleOriginalAnchorCertificateBatch30.anchors ++ MiddleOriginalAnchorCertificateBatch31.anchors ++ MiddleOriginalAnchorCertificateBatch32.anchors ++ MiddleOriginalAnchorCertificateBatch33.anchors
theorem original_data_exact : DegreeOneMiddleAnchors.anchors.toList=certificateAnchors := by decide +kernel
theorem all_proved : ∀ a ∈ certificateAnchors, Proved a := by
  intro a ha
  simp only [certificateAnchors,List.mem_append] at ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch00.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch01.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch02.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch03.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch04.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch05.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch06.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch07.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch08.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch09.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch10.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch11.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch12.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch13.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch14.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch15.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch16.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch17.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch18.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch19.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch20.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch21.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch22.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch23.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch24.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch25.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch26.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch27.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch28.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch29.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch30.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch31.all_proved a ha
  rcases ha with ha | ha
  · exact MiddleOriginalAnchorCertificateBatch32.all_proved a ha
  exact MiddleOriginalAnchorCertificateBatch33.all_proved a ha
theorem analytic_certificates : DegreeOneMiddleAnchors.AnalyticCertificates := by
  intro a ha
  rw [original_data_exact] at ha
  exact all_proved a ha
theorem input_family (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ)
    (hT : (source C u p q).IsTree) (hd : C.degree u=1)
    (h14 : 14≤order C p q) (h52 : order C p q≤52) :
    0<meanIntegral C u p q :=
  DegreeOneMiddleAnchors.input_family_of_certificates DegreeOneMiddleAnchors.complete
    analytic_certificates DegreeOneMiddleResidualFiniteAllCertificates.residual_cases
    m C u p q hT hd h14 h52
#print axioms original_data_exact
#print axioms all_proved
#print axioms analytic_certificates
#print axioms input_family
end
end Gebendorfer.RadenkovicGutman.OriginalDegreeOneMiddle
