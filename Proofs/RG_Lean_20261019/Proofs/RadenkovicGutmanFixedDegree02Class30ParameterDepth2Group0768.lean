/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3072
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3073
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3074
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3075

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0768
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3072.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3073.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3074.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3075.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(151/3200),(1211/25600),(-7785855791272954479357/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (151/3200) (1211/25600) 0 1 0 1 (-7785855791272954479357/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3072.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3073.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3074.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3075.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0768
