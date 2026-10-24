/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4232
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4233
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4234
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4235

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1058
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4232.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4233.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4234.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4235.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(109/640),(11/64),(-159173795978304719103/295147905179352825856)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (109/640) (11/64) 0 1 0 1 (-159173795978304719103/295147905179352825856) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4232.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4233.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4234.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4235.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1058
