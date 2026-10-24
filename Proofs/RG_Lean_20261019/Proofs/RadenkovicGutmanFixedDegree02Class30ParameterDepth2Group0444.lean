/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1776
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1777
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1778
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1779

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0444
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1776.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1777.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1778.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1779.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(223/12800),(7/400),(-3222828378767200944147/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (223/12800) (7/400) 0 1 0 1 (-3222828378767200944147/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1776.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1777.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1778.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1779.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0444
