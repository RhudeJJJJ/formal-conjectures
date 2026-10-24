/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1472
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1473
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1474
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1475

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0368
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1472.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1473.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1474.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1475.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(169/12800),(339/25600),(-14478890871456870542573/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (169/12800) (339/25600) 0 1 0 1 (-14478890871456870542573/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1472.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1473.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1474.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1475.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0368
