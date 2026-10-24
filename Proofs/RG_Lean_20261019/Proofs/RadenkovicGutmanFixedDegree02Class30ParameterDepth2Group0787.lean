/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3148
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3149
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3150
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3151

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0787
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3148.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3149.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3150.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3151.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(253/5120),(317/6400),(-3784578372197088378845/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (253/5120) (317/6400) 0 1 0 1 (-3784578372197088378845/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3148.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3149.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3150.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3151.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0787
