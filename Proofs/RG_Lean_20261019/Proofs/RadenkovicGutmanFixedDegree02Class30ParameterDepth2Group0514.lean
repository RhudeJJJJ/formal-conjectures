/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2056
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2057
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2058
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2059

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0514
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2056.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2057.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2058.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2059.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(227/10240),(569/25600),(-11574883100735230398919/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (227/10240) (569/25600) 0 1 0 1 (-11574883100735230398919/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2056.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2057.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2058.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2059.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0514
