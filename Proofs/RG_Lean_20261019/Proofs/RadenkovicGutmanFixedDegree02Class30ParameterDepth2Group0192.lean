/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0768
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0769
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0770
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0771

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0192
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0768.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0769.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0770.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0771.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(81/12800),(163/25600),(-2376258918578521078927/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (81/12800) (163/25600) 0 1 0 1 (-2376258918578521078927/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0768.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0769.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0770.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0771.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0192
