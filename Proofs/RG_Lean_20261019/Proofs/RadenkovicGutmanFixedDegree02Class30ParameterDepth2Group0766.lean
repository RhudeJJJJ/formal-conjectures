/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3064
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3065
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3066
import Proofs.RadenkovicGutmanFixedDegree02Class30ParameterDepth2Leaf3067

namespace Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0766
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.second (1/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3064.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3065.cell)) (.second (3/4) (.leaf FixedDegree02Class30ParameterDepth2Leaf3066.cell) (.leaf FixedDegree02Class30ParameterDepth2Leaf3067.cell))
def slice : FastArmCoverIntegral.Slice := ⟨cover,(601/12800),(241/5120),(-244042206395140748247/147573952589676412928)⟩
theorem cover_checked : FastArmCover.accepts 2 2 4 (601/12800) (241/5120) 0 1 0 1 (-244042206395140748247/147573952589676412928) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨⟨FixedDegree02Class30ParameterDepth2Leaf3064.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3065.checked,by decide +kernel,by decide +kernel⟩⟩,⟨⟨FixedDegree02Class30ParameterDepth2Leaf3066.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree02Class30ParameterDepth2Leaf3067.checked,by decide +kernel,by decide +kernel⟩⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 2 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 2 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree02Class30ParameterDepth2Group0766
