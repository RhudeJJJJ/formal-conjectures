/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0040
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0041
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0042
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0043

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0010
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0040.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0041.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0042.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0043.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(19/16000),(39/32000),(-3786636421071028350721/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (19/16000) (39/32000) 0 1 0 1 (-3786636421071028350721/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0040.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0041.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0042.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0043.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0010
