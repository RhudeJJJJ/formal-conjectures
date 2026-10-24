/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4692
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4693
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4694
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4695

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1173
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4692.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4693.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4694.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4695.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(64/13),(256/51),(254248170789053921533/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (64/13) (256/51) 0 1 0 1 (254248170789053921533/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4692.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4693.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4694.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4695.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1173
