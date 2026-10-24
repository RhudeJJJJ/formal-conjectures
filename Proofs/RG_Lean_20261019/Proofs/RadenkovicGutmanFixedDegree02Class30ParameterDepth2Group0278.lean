/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1112
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1113
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1114
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1115

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0278
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1112.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1113.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1114.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1115.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(31/3200),(249/25600),(-4083691849716065351609/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (31/3200) (249/25600) 0 1 0 1 (-4083691849716065351609/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1112.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1113.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1114.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1115.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0278
