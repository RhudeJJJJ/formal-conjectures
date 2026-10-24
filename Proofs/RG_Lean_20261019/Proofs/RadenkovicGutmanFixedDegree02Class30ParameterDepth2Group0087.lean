/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0348
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0349
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0350
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0351

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0087
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0348.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0349.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0350.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0351.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(409/128000),(103/32000),(-23519337745633640335981/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (409/128000) (103/32000) 0 1 0 1 (-23519337745633640335981/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0348.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0349.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0350.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0351.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0087
