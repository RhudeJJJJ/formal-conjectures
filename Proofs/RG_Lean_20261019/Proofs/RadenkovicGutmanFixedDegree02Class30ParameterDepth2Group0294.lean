/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1176
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1177
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1178
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1179

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0294
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1176.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1177.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1178.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1179.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(33/3200),(53/5120),(-1994169450758804111781/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (33/3200) (53/5120) 0 1 0 1 (-1994169450758804111781/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1176.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1177.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1178.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1179.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0294
