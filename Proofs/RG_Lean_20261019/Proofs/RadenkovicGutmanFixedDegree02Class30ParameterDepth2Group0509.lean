/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2036
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2037
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2038
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2039

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0509
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2036.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2037.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2038.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2039.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(7/320),(1123/51200),(-363941172031999026521/147573952589676412928)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (7/320) (1123/51200) 0 1 0 1 (-363941172031999026521/147573952589676412928) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2036.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2037.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2038.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2039.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0509
