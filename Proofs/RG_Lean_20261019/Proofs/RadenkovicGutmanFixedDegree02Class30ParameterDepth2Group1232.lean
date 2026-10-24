/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4928
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4929
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4930
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4931

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1232
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4928.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4929.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4930.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4931.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(256/11),(512/21),(15354745185062880489/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (256/11) (512/21) 0 1 0 1 (15354745185062880489/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4928.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4929.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4930.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4931.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1232
