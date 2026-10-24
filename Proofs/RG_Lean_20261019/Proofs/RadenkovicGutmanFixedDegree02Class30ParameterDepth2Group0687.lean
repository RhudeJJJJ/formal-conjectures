/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2748
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2749
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2750
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2751

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0687
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2748.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2749.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2750.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2751.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(193/5120),(121/3200),(-553980892040964194213/295147905179352825856)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (193/5120) (121/3200) 0 1 0 1 (-553980892040964194213/295147905179352825856) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2748.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2749.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2750.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2751.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0687
