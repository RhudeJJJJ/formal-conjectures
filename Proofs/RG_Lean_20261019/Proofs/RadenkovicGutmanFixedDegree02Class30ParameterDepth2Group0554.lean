/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2216
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2217
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2218
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2219

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0554
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2216.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2217.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2218.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2219.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(251/10240),(629/25600),(-5521125609511735743241/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (251/10240) (629/25600) 0 1 0 1 (-5521125609511735743241/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2216.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2217.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2218.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2219.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0554
