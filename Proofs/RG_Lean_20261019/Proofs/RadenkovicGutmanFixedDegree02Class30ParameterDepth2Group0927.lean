/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3708
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3709
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3710
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3711

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0927
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3708.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3709.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3710.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3711.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(51/640),(41/512),(-677447621081340674083/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (51/640) (41/512) 0 1 0 1 (-677447621081340674083/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3708.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3709.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3710.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3711.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0927
