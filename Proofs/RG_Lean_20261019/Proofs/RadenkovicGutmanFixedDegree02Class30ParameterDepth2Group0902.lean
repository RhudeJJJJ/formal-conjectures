/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3608
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3609
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3610
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3611

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0902
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3608.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3609.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3610.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3611.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(183/2560),(367/5120),(-11506724389833769455/9223372036854775808)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (183/2560) (367/5120) 0 1 0 1 (-11506724389833769455/9223372036854775808) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3608.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3609.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3610.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3611.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0902
