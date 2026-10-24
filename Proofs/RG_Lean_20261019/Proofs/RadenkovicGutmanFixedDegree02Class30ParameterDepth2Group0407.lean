/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1628
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1629
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1630
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1631

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0407
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1628.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1629.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1630.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1631.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(377/25600),(189/12800),(-3461284657272312711209/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (377/25600) (189/12800) 0 1 0 1 (-3461284657272312711209/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1628.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1629.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1630.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1631.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0407
