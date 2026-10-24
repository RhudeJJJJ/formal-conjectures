/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1084
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1085
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1086
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1087

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0271
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1084.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1085.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1086.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1087.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(241/25600),(121/12800),(-16510496608295272711459/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (241/25600) (121/12800) 0 1 0 1 (-16510496608295272711459/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1084.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1085.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1086.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1087.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0271
