/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1232
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1233
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1234
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1235

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0308
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1232.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1233.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1234.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1235.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(139/12800),(279/25600),(-7820291805317009543561/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (139/12800) (279/25600) 0 1 0 1 (-7820291805317009543561/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1232.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1233.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1234.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1235.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0308
