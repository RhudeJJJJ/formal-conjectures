/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5068
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5069
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5070
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf5071

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1267
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf5068.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf5069.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf5070.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf5071.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1024/7),(2048/13),(379216320462414187/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (1024/7) (2048/13) 0 1 0 1 (379216320462414187/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf5068.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf5069.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf5070.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf5071.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1267
