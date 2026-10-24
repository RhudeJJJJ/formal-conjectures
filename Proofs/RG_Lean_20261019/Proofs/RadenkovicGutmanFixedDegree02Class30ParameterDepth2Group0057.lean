/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0228
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0229
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0230
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0231

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0057
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0228.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0229.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0230.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0231.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(319/128000),(161/64000),(-6300523186582511270283/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (319/128000) (161/64000) 0 1 0 1 (-6300523186582511270283/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0228.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0229.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0230.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0231.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0057
