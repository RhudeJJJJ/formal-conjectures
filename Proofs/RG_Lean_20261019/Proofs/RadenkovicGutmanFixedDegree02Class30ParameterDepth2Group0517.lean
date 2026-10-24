/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2068
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2069
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2070
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2071

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0517
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2068.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2069.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2070.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2071.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(143/6400),(1147/51200),(-720792132294700774371/295147905179352825856)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (143/6400) (1147/51200) 0 1 0 1 (-720792132294700774371/295147905179352825856) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2068.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2069.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2070.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2071.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0517
