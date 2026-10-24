/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2432
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2433
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2434
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2435

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0608
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2432.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2433.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2434.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2435.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(91/3200),(731/25600),(-641986050235007985027/295147905179352825856)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (91/3200) (731/25600) 0 1 0 1 (-641986050235007985027/295147905179352825856) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2432.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2433.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2434.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2435.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0608
