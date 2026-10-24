/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4184
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4185
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4186
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4187

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1046
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4184.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4185.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4186.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4187.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(97/640),(49/320),(-2925785737497314486413/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (97/640) (49/320) 0 1 0 1 (-2925785737497314486413/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4184.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4185.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4186.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4187.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1046
