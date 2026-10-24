/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2844
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2845
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2846
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2847

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0711
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2844.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2845.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2846.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2847.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1037/25600),(13/320),(-1064285424938962175859/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (1037/25600) (13/320) 0 1 0 1 (-1064285424938962175859/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2844.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2845.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2846.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2847.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0711
