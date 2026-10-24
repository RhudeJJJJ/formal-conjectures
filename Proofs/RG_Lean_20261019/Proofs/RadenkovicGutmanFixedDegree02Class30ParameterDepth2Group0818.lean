/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3272
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3273
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3274
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3275

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0818
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3272.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3273.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3274.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3275.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(141/2560),(283/5120),(-3532585703597820930293/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (141/2560) (283/5120) 0 1 0 1 (-3532585703597820930293/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3272.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3273.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3274.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3275.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0818
