/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3944
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3945
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3946
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3947

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0986
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3944.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3945.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3946.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3947.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(263/2560),(33/320),(-2182408881078169358815/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (263/2560) (33/320) 0 1 0 1 (-2182408881078169358815/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3944.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3945.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3946.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3947.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0986
