/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1304
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1305
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1306
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1307

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0326
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1304.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1305.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1306.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1307.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(37/3200),(297/25600),(-1907989246077809031127/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (37/3200) (297/25600) 0 1 0 1 (-1907989246077809031127/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1304.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1305.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1306.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1307.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0326
