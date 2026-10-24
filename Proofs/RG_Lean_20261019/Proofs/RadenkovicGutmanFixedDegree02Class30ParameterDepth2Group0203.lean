/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0812
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0813
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0814
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0815

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0203
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0812.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0813.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0814.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0815.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(173/25600),(87/12800),(-18589358791739408530165/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (173/25600) (87/12800) 0 1 0 1 (-18589358791739408530165/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0812.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0813.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0814.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0815.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0203
