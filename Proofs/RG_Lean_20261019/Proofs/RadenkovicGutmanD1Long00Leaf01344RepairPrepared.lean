/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01344_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 13225868610224154214400000000000 15236704726482199929903565664509 989593204463877800287000000000000))
theorem leaf01344_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 13225868610224154214400000000000 15236704726482199929903565664509 989593204463877800287000000000000 leaf01344_w_raw=true := by decide +kernel
theorem leaf01344_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01344_w_raw=true := by decide +kernel
#print axioms leaf01344_raw
#print axioms leaf01344_rectangular
noncomputable def leaf01344_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01344_w_raw ![11,1,0] ![1,1,1] ![32,2,2])
theorem leaf01344_inner : leaf01344_w_inner=IntegerAffineStages.inner leaf01344_w_raw ![11,1,0] ![1,1,1] ![32,2,2] := by decide +kernel
#print axioms leaf01344_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
