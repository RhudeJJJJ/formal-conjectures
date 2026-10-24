/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4128
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4129
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4130
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4131

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1032
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4128.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4129.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4130.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4131.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(87/640),(35/256),(-1651402262305405287911/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (87/640) (35/256) 0 1 0 1 (-1651402262305405287911/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4128.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4129.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4130.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4131.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1032
