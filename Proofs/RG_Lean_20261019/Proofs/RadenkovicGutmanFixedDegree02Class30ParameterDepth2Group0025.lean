/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0100
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0101
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0102
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0103

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0025
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0100.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0101.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0102.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0103.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(53/32000),(27/16000),(-13997884977450798543665/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (53/32000) (27/16000) 0 1 0 1 (-13997884977450798543665/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0100.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0101.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0102.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0103.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0025
