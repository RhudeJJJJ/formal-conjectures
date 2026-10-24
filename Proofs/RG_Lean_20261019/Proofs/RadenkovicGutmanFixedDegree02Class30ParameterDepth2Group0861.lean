/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3444
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3445
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3446
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3447

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0861
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3444.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3445.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3446.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3447.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(65/1024),(163/2560),(-3209757203435861975435/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (65/1024) (163/2560) 0 1 0 1 (-3209757203435861975435/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3444.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3445.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3446.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3447.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0861
