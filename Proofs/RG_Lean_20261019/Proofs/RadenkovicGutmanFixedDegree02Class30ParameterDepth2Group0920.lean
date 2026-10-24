/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3680
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3681
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3682
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3683

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0920
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3680.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3681.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3682.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3683.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(197/2560),(99/1280),(-696251939800077935619/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (197/2560) (99/1280) 0 1 0 1 (-696251939800077935619/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3680.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3681.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3682.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3683.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0920
