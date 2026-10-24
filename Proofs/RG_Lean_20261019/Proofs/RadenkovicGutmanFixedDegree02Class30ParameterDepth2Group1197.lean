/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4788
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4789
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4790
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf4791

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1197
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4788.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4789.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf4790.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf4791.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(512/57),(64/7),(24343890447996546465/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (512/57) (64/7) 0 1 0 1 (24343890447996546465/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf4788.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4789.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf4790.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf4791.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group1197
