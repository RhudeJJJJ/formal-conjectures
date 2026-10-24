/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4268
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4269
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4270
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4271

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1067
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4268.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4269.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4270.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4271.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(59/320),(3/16),(-1152601540767445617383/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (59/320) (3/16) 0 1 0 1 (-1152601540767445617383/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4268.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4269.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4270.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4271.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1067
