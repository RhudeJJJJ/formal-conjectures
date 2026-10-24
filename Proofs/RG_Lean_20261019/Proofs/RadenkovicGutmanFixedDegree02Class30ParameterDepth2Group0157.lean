/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0628
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0629
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0630
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0631

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0157
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0628.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0629.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0630.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0631.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(317/64000),(1/200),(-20599028097891031228159/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (317/64000) (1/200) 0 1 0 1 (-20599028097891031228159/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0628.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0629.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0630.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0631.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0157
