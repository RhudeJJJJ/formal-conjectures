/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2440
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2441
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2442
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2443

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0610
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2440.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2441.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2442.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2443.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(367/12800),(737/25600),(-2557455846450325318415/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (367/12800) (737/25600) 0 1 0 1 (-2557455846450325318415/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2440.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2441.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2442.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2443.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0610
