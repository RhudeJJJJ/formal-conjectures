/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0250
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1Leaf0251

namespace Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0125
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
def cover : FastArmCover.Cover := .second (1/2) (.leaf FixedDegree03Class30ParameterDepth1Leaf0250.cell) (.leaf FixedDegree03Class30ParameterDepth1Leaf0251.cell)
def slice : FastArmCoverIntegral.Slice := ⟨cover,(97/6400),(49/3200),(-7307083081731075043029/2361183241434822606848)⟩
theorem cover_checked : FastArmCover.accepts 3 2 4 (97/6400) (49/3200) 0 1 0 1 (-7307083081731075043029/2361183241434822606848) cover=true := by
  simp only [cover,FastArmCover.accepts,Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨⟨FixedDegree03Class30ParameterDepth1Leaf0250.checked,by decide +kernel,by decide +kernel⟩,⟨FixedDegree03Class30ParameterDepth1Leaf0251.checked,by decide +kernel,by decide +kernel⟩⟩
theorem slice_checked : FastArmCoverIntegral.accepts 3 2 4 slice=true :=
  FastArmCoverIntegral.accepts_of_checks 3 2 4 slice (by decide +kernel) (by decide +kernel) cover_checked
#print axioms cover_checked
#print axioms slice_checked
end Gebendorfer.RadenkovicGutman.FixedDegree03Class30ParameterDepth1Group0125
