/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2116
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2117
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2118
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2119

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0529
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2116.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2117.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2118.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2119.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(59/2560),(1183/51200),(-2841919082702055097293/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (59/2560) (1183/51200) 0 1 0 1 (-2841919082702055097293/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2116.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2117.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2118.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2119.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0529
