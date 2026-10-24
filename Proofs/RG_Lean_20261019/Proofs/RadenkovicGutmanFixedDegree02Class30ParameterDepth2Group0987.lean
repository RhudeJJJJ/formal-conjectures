/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3948
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3949
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3950
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3951

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0987
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3948.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3949.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3950.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3951.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(33/320),(53/512),(-1087413004387310193251/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (33/320) (53/512) 0 1 0 1 (-1087413004387310193251/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3948.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3949.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3950.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3951.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0987
