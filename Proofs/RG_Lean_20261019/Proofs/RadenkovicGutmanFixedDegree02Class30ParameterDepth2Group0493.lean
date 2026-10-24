/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1972
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1973
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1974
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1975

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0493
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1972.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1973.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1974.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1975.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(67/3200),(43/2048),(-5940935554330009103447/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (67/3200) (43/2048) 0 1 0 1 (-5940935554330009103447/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1972.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1973.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1974.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1975.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0493
