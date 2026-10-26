/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate274
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate275
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate276
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate279
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate280
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate283
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate284
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate370
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate371
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate572
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate606
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate607
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificate610
namespace Gebendorfer.RadenkovicGutman.MiddleOtherOrders13Original
open MiddleOriginalAnchorPredicate DegreeOneMiddleAnchors
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
def anchors : List Anchor := [MiddleOriginalAnchorCertificate274.anchor,MiddleOriginalAnchorCertificate275.anchor,MiddleOriginalAnchorCertificate276.anchor,MiddleOriginalAnchorCertificate279.anchor,MiddleOriginalAnchorCertificate280.anchor,MiddleOriginalAnchorCertificate283.anchor,MiddleOriginalAnchorCertificate284.anchor,MiddleOriginalAnchorCertificate370.anchor,MiddleOriginalAnchorCertificate371.anchor,MiddleOriginalAnchorCertificate572.anchor,MiddleOriginalAnchorCertificate606.anchor,MiddleOriginalAnchorCertificate607.anchor,MiddleOriginalAnchorCertificate610.anchor]
def original_entries : List Anchor := [DegreeOneMiddleAnchors.anchors[274]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[275]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[276]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[279]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[280]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[283]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[284]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[370]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[371]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[572]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[606]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[607]'(by decide +kernel),DegreeOneMiddleAnchors.anchors[610]'(by decide +kernel)]
theorem original_data_exact : original_entries=anchors := by decide +kernel
theorem all_proved : ∀ a∈anchors, Proved a := by
  simp only [anchors,List.forall_mem_cons]
  exact ⟨MiddleOriginalAnchorCertificate274.certificate,MiddleOriginalAnchorCertificate275.certificate,MiddleOriginalAnchorCertificate276.certificate,MiddleOriginalAnchorCertificate279.certificate,MiddleOriginalAnchorCertificate280.certificate,MiddleOriginalAnchorCertificate283.certificate,MiddleOriginalAnchorCertificate284.certificate,MiddleOriginalAnchorCertificate370.certificate,MiddleOriginalAnchorCertificate371.certificate,MiddleOriginalAnchorCertificate572.certificate,MiddleOriginalAnchorCertificate606.certificate,MiddleOriginalAnchorCertificate607.certificate,MiddleOriginalAnchorCertificate610.certificate,fun _ h => False.elim (List.not_mem_nil h)⟩
theorem original_entries_proved : ∀ a∈original_entries, Proved a := by
  rw [original_data_exact]
  exact all_proved
#print axioms original_data_exact
#print axioms all_proved
#print axioms original_entries_proved
end
end Gebendorfer.RadenkovicGutman.MiddleOtherOrders13Original
