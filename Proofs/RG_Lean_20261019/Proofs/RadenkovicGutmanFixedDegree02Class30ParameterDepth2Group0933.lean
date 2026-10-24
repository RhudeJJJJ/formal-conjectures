/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3732
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3733
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3734
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3735

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0933
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3732.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3733.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3734.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3735.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(21/256),(211/2560),(-20685973552468110013/18446744073709551616)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (21/256) (211/2560) 0 1 0 1 (-20685973552468110013/18446744073709551616) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3732.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3733.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3734.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3735.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0933
