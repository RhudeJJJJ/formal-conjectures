/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3276
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3277
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3278
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3279

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0819
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3276.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3277.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3278.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3279.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(283/5120),(71/1280),(-220277519700763267777/147573952589676412928)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (283/5120) (71/1280) 0 1 0 1 (-220277519700763267777/147573952589676412928) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3276.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3277.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3278.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3279.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0819
