/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3820
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3821
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3822
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3823

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0955
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3820.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3821.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3822.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3823.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(29/320),(233/2560),(-152383663762626977567/147573952589676412928)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (29/320) (233/2560) 0 1 0 1 (-152383663762626977567/147573952589676412928) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3820.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3821.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3822.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3823.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0955
