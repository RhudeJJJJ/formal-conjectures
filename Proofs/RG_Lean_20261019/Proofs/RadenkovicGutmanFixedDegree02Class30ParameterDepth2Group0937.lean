/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3748
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3749
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3750
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3751

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0937
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3748.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3749.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3750.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3751.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(107/1280),(43/512),(-651921964998927816705/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (107/1280) (43/512) 0 1 0 1 (-651921964998927816705/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3748.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3749.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3750.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3751.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0937
