/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0916
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0917
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0918
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0919

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0229
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0916.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0917.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0918.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0919.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(199/25600),(1/128),(-2212737429492208591123/590295810358705651712)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (199/25600) (1/128) 0 1 0 1 (-2212737429492208591123/590295810358705651712) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0916.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0917.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0918.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0919.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0229
