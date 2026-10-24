/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4140
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4141
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4142
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4143

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1035
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4140.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4141.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4142.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4143.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(177/1280),(89/640),(-405263823835891501035/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (177/1280) (89/640) 0 1 0 1 (-405263823835891501035/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4140.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4141.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4142.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4143.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1035
