/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0008
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0009

namespace Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0004
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.leaf FixedDegree03Class30ParameterDepth1Leaf0008.cell) (.leaf FixedDegree03Class30ParameterDepth1Leaf0009.cell)
def slice : FastArmCoverIntegral.Slice := ⟨cover,(1/800),(21/16000),(-31533239191660379933401/4722366482869645213696)⟩
theorem cover_checked : FastArmCover.accepts 3 2 4 (1/800) (21/16000) 0 1 0 1 (-31533239191660379933401/4722366482869645213696) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨FixedDegree03Class30ParameterDepth1Leaf0008.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree03Class30ParameterDepth1Leaf0009.checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 3 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 3 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0004
