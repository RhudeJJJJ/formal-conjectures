/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3628
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3629
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3630
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3631

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0907
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3628.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3629.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3630.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3631.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(371/5120),(93/1280),(-728988543739009099197/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (371/5120) (93/1280) 0 1 0 1 (-728988543739009099197/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3628.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3629.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3630.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3631.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0907
