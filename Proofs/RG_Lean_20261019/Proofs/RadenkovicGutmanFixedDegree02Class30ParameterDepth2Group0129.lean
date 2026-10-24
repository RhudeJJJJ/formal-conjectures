/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0516
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0517
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0518
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0519

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0129
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0516.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0517.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0518.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0519.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(107/25600),(269/64000),(-21723599192097964461561/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (107/25600) (269/64000) 0 1 0 1 (-21723599192097964461561/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0516.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0517.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0518.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0519.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0129
