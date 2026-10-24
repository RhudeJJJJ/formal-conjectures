/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1976
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1977
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1978
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1979

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0494
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1976.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1977.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1978.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1979.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(43/2048),(539/25600),(-11866774070929697647837/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (43/2048) (539/25600) 0 1 0 1 (-11866774070929697647837/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1976.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1977.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1978.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1979.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0494
