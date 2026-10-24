/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1788
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1789
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1790
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1791

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0447
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1788.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1789.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1790.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1791.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(113/6400),(227/12800),(-12816777921894935807617/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (113/6400) (227/12800) 0 1 0 1 (-12816777921894935807617/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1788.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1789.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1790.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1791.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0447
