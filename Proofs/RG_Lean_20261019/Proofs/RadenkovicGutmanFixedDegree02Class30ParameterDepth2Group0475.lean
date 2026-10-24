/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1900
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1901
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1902
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1903

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1900.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1901.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1902.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1903.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(127/6400),(51/2560),(-12172832107154213586903/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (127/6400) (51/2560) 0 1 0 1 (-12172832107154213586903/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1900.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1901.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1902.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1903.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0475
