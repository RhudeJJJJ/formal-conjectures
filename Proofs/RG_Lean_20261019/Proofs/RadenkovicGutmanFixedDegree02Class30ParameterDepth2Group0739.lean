/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2956
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2957
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2958
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2959

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0739
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2956.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2957.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2958.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2959.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1121/25600),(281/6400),(-8140435926817305924797/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (1121/25600) (281/6400) 0 1 0 1 (-8140435926817305924797/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2956.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2957.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2958.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2959.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0739
