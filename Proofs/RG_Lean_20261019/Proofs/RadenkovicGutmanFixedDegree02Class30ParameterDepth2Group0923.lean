/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3692
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3693
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3694
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3695

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0923
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3692.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3693.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3694.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3695.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(5/64),(201/2560),(-2752376714632320115783/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (5/64) (201/2560) 0 1 0 1 (-2752376714632320115783/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3692.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3693.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3694.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3695.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0923
