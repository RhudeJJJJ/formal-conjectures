/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4848
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4849
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4850
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4851

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1212
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4848.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4849.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4850.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4851.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(256/21),(512/41),(55280501004787111191/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (256/21) (512/41) 0 1 0 1 (55280501004787111191/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4848.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4849.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4850.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4851.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1212
