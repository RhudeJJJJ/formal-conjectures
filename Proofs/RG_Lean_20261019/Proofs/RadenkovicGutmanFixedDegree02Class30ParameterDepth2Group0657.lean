/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2628
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2629
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2630
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2631

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0657
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2628.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2629.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2630.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2631.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(35/1024),(439/12800),(-4672749848908320372433/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (35/1024) (439/12800) 0 1 0 1 (-4672749848908320372433/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2628.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2629.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2630.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2631.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0657
