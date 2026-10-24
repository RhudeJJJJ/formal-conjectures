/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1168
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1169
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1170
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1171

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0292
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1168.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1169.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1170.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1171.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(131/12800),(263/25600),(-1999947021909744031405/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (131/12800) (263/25600) 0 1 0 1 (-1999947021909744031405/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1168.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1169.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1170.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1171.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0292
