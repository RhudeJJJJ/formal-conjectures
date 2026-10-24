/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2916
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2917
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2918
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2919

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0729
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2916.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2917.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2918.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2919.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1091/25600),(547/12800),(-2067531995539923279803/1180591620717411303424)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (1091/25600) (547/12800) 0 1 0 1 (-2067531995539923279803/1180591620717411303424) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2916.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2917.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2918.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2919.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0729
