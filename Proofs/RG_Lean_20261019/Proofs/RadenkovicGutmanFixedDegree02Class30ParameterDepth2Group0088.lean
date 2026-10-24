/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0352
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0353
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0354
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf0355

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0088
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0352.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0353.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf0354.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf0355.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(103/32000),(83/25600),(-23470132734841212204071/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (103/32000) (83/25600) 0 1 0 1 (-23470132734841212204071/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf0352.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0353.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf0354.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf0355.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0088
