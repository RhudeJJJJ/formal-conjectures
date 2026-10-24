/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0036
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0037
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0038
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0039

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0009
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0036.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0037.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0038.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0039.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(37/32000),(19/16000),(-15238890701601011664077/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (37/32000) (19/16000) 0 1 0 1 (-15238890701601011664077/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0036.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0037.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0038.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0039.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0009
