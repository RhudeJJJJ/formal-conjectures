/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5116
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5117
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5118
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5119

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1279
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf5116.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf5117.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf5118.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf5119.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(4096/7),(2048/3),(20250577485840287/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (4096/7) (2048/3) 0 1 0 1 (20250577485840287/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf5116.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf5117.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf5118.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf5119.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1279
