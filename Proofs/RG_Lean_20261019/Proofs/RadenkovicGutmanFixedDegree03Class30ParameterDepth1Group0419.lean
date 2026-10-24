/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0838
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0839

namespace Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0419
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.leaf FixedDegree03Class30ParameterDepth1Leaf0838.cell) (.leaf FixedDegree03Class30ParameterDepth1Leaf0839.cell)
def slice : FastArmCoverIntegral.Slice := ⟨cover,(19/80),(79/320),(-103105977224107804963/295147905179352825856)⟩
theorem cover_checked : FastArmCover.accepts 3 2 4 (19/80) (79/320) 0 1 0 1 (-103105977224107804963/295147905179352825856) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨FixedDegree03Class30ParameterDepth1Leaf0838.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree03Class30ParameterDepth1Leaf0839.checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 3 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 3 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0419
