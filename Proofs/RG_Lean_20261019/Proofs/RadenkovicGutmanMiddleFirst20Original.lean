/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMiddleOriginalAnchorCertificateBatch00

/-! The first twenty entries of the original middle-order anchor catalogue,
with their original actual-tree integral bounds. -/
namespace Gebendorfer.RadenkovicGutman.MiddleFirst20Original
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem original_data_exact :
    DegreeOneMiddleAnchors.anchors.toList.take 20 =
      MiddleOriginalAnchorCertificateBatch00.anchors := by decide +kernel

theorem original_prefix_proved :
    ∀ a ∈ DegreeOneMiddleAnchors.anchors.toList.take 20,
      MiddleOriginalAnchorPredicate.Proved a := by
  rw [original_data_exact]
  exact MiddleOriginalAnchorCertificateBatch00.all_proved

#print axioms original_data_exact
#print axioms original_prefix_proved
end Gebendorfer.RadenkovicGutman.MiddleFirst20Original
