/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0828
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0829
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0830
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0831

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0207
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0828.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0829.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0830.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0831.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(177/25600),(89/12800),(-9221800605199663155023/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (177/25600) (89/12800) 0 1 0 1 (-9221800605199663155023/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0828.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0829.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0830.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0831.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0207
