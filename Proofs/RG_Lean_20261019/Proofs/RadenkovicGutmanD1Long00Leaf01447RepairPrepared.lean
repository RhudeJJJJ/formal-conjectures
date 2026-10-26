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
noncomputable def leaf01447_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 1238049757438830182400000000000 1345485347544692681325975347097 233383817178170638881500000000000))
theorem leaf01447_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 1238049757438830182400000000000 1345485347544692681325975347097 233383817178170638881500000000000 leaf01447_w_raw=true := by decide +kernel
theorem leaf01447_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01447_w_raw=true := by decide +kernel
#print axioms leaf01447_raw
#print axioms leaf01447_rectangular
noncomputable def leaf01447_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01447_w_raw ![15,2,1] ![1,1,1] ![64,4,2])
theorem leaf01447_inner : leaf01447_w_inner=IntegerAffineStages.inner leaf01447_w_raw ![15,2,1] ![1,1,1] ![64,4,2] := by decide +kernel
#print axioms leaf01447_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
