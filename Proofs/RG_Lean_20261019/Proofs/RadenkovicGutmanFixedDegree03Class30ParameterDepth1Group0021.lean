/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0042
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0043

namespace Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0021
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.leaf FixedDegree03Class30ParameterDepth1Leaf0042.cell) (.leaf FixedDegree03Class30ParameterDepth1Leaf0043.cell)
def slice : FastArmCoverIntegral.Slice := ⟨cover,(79/32000),(41/16000),(-837174679783162170191/147573952589676412928)⟩
theorem cover_checked : FastArmCover.accepts 3 2 4 (79/32000) (41/16000) 0 1 0 1 (-837174679783162170191/147573952589676412928) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨FixedDegree03Class30ParameterDepth1Leaf0042.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree03Class30ParameterDepth1Leaf0043.checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 3 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 3 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0021
