/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3928
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3929
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3930
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3931

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0982
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3928.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3929.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3930.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3931.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(259/2560),(13/128),(-1106564136179120315537/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (259/2560) (13/128) 0 1 0 1 (-1106564136179120315537/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3928.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3929.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3930.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3931.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0982
