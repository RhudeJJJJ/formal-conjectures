/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4020
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4021
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4022
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4023

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1005
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4020.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4021.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4022.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4023.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(147/1280),(37/320),(-3927923499628633649143/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (147/1280) (37/320) 0 1 0 1 (-3927923499628633649143/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4020.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4021.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4022.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4023.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1005
