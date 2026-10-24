/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1932
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1933
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1934
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1935

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0483
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1932.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1933.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1934.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1935.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(521/25600),(209/10240),(-6017821319432469174539/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (521/25600) (209/10240) 0 1 0 1 (-6017821319432469174539/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1932.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1933.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1934.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1935.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0483
