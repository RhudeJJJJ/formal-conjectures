/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2244
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2245
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2246
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2247

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0561
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2244.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2245.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2246.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2247.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(319/12800),(1279/51200),(-5477613779350206126733/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (319/12800) (1279/51200) 0 1 0 1 (-5477613779350206126733/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2244.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2245.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2246.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2247.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0561
