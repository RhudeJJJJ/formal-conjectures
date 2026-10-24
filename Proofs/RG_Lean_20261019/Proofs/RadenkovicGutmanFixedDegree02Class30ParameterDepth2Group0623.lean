/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2492
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2493
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2494
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf2495

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0623
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2492.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2493.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf2494.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf2495.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(773/25600),(97/3200),(-9966565320063297432507/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (773/25600) (97/3200) 0 1 0 1 (-9966565320063297432507/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf2492.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2493.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf2494.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf2495.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0623
