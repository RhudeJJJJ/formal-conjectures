/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4496
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4497
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4498
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4499

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1124
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4496.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4497.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4498.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4499.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(29/32),(15/16),(105099500195978214111/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (29/32) (15/16) 0 1 0 1 (105099500195978214111/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4496.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4497.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4498.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4499.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1124
