/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3464
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3465
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3466
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3467

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0866
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3464.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3465.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3466.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3467.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(33/512),(331/5120),(-3175497538053627473189/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (33/512) (331/5120) 0 1 0 1 (-3175497538053627473189/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3464.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3465.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3466.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3467.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0866
