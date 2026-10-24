/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4428
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4429
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4430
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4431

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1107
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4428.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4429.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4430.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4431.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(77/160),(1/2),(-398466390117003867935/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (77/160) (1/2) 0 1 0 1 (-398466390117003867935/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4428.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4429.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4430.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4431.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1107
