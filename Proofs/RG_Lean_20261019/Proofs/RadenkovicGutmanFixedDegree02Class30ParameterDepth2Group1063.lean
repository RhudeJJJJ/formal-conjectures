/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4252
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4253
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4254
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4255

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1063
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4252.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4253.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4254.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4255.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(57/320),(23/128),(-2408427067384907392351/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (57/320) (23/128) 0 1 0 1 (-2408427067384907392351/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4252.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4253.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4254.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4255.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1063
