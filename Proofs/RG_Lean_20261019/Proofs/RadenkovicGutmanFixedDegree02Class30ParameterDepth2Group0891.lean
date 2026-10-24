/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3564
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3565
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3566
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3567

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0891
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3564.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3565.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3566.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3567.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(71/1024),(89/1280),(-3012964743497757519493/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (71/1024) (89/1280) 0 1 0 1 (-3012964743497757519493/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3564.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3565.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3566.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3567.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0891
