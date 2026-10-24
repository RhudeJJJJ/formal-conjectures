/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3192
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3193
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3194
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3195

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0798
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3192.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3193.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3194.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3195.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(131/2560),(263/5120),(-3702904375247028014761/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (131/2560) (263/5120) 0 1 0 1 (-3702904375247028014761/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3192.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3193.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3194.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3195.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0798
