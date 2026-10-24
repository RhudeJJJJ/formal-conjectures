/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2724
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2725
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2726
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2727

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0681
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2724.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2725.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2726.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2727.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(947/25600),(19/512),(-8955773603514827690651/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (947/25600) (19/512) 0 1 0 1 (-8955773603514827690651/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2724.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2725.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2726.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2727.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0681
