/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3168
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3169
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3170
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3171

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0792
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3168.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3169.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3170.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3171.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/20),(257/5120),(-1878476221551881326031/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (1/20) (257/5120) 0 1 0 1 (-1878476221551881326031/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3168.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3169.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3170.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3171.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0792
