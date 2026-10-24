/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1000
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1001
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1002
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1003

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0250
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1000.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1001.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1002.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1003.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(11/1280),(221/25600),(-2134289855068965399985/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (11/1280) (221/25600) 0 1 0 1 (-2134289855068965399985/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1000.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1001.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1002.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1003.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0250
