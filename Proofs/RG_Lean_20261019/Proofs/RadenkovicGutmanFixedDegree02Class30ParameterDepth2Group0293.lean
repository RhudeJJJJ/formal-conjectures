/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1172
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1173
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1174
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf1175

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0293
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1172.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1173.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf1174.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf1175.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(263/25600),(33/3200),(-124815749462665028871/36893488147419103232)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (263/25600) (33/3200) 0 1 0 1 (-124815749462665028871/36893488147419103232) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf1172.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1173.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf1174.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf1175.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0293
