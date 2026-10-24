/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1256
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1257
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1258
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1259

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0314
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1256.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1257.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1258.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1259.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(71/6400),(57/5120),(-484749952524335467769/147573952589676412928)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (71/6400) (57/5120) 0 1 0 1 (-484749952524335467769/147573952589676412928) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1256.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1257.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1258.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1259.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0314
