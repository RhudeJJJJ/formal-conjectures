/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4628
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4629
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4630
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4631

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1157
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4628.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4629.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4630.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4631.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(64/19),(128/37),(49360091392526806439/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (64/19) (128/37) 0 1 0 1 (49360091392526806439/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4628.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4629.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4630.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4631.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1157
