/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4652
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4653
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4654
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4655

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1163
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4652.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4653.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4654.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4655.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,4,(128/31),(326741586705167804969/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 4 (128/31) 0 1 0 1 (326741586705167804969/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4652.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4653.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4654.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4655.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1163
