/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1504
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1505
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1506
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1507

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0376
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1504.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1505.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1506.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1507.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(173/12800),(347/25600),(-14342174426866709604367/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (173/12800) (347/25600) 0 1 0 1 (-14342174426866709604367/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1504.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1505.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1506.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1507.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0376
