/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1656
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1657
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1658
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1659

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0414
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1656.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1657.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1658.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1659.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(193/12800),(97/6400),(-107096930292343210775/36893488147419103232)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (193/12800) (97/6400) 0 1 0 1 (-107096930292343210775/36893488147419103232) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1656.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1657.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1658.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1659.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0414
