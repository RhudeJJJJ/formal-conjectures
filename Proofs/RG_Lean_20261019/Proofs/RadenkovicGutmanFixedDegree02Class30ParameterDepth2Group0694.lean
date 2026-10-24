/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2776
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2777
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2778
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2779

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0694
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2776.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2777.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2778.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2779.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(493/12800),(989/25600),(-2189687071210194706567/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (493/12800) (989/25600) 0 1 0 1 (-2189687071210194706567/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2776.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2777.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2778.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2779.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0694
