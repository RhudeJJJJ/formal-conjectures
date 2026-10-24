/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class00Depth2PrunedControlLeaf6289

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class00Depth2PrunedControlGroup1344
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def cover : FastArmCover.Cover := .leaf FixedDegree02Class00Depth2PrunedControlLeaf6289.cell
noncomputable def slice : FastArmCoverIntegral.Slice := ⟨cover,(4096/5),1024,(9002455132689133/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 4 4 (4096/5) 1024 0 1 0 1 (9002455132689133/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨FixedDegree02Class00Depth2PrunedControlLeaf6289.checked,by decide +kernel,by decide +kernel⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 4 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 4 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class00Depth2PrunedControlGroup1344
