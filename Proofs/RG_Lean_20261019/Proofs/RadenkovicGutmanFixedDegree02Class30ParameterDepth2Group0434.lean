/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1736
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1737
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1738
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1739

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0434
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1736.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1737.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1738.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1739.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(213/12800),(107/6400),(-3287139255595491347201/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (213/12800) (107/6400) 0 1 0 1 (-3287139255595491347201/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1736.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1737.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1738.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1739.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0434
