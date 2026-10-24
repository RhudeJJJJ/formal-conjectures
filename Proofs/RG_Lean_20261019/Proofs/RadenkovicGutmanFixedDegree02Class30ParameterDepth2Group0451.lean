/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1804
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1805
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1806
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1807

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0451
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1804.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1805.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1806.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1807.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(23/1280),(231/12800),(-3179797470754741809215/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (23/1280) (231/12800) 0 1 0 1 (-3179797470754741809215/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1804.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1805.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1806.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1807.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0451
