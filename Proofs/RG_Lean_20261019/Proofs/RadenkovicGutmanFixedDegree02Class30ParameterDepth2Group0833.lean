/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3332
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3333
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3334
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3335

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0833
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3332.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3333.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3334.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3335.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(297/5120),(149/2560),(-3413801262658179389701/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (297/5120) (149/2560) 0 1 0 1 (-3413801262658179389701/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3332.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3333.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3334.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3335.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0833
