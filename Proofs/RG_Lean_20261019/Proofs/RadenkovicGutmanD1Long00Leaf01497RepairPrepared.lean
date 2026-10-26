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
noncomputable def leaf01497_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 108565403122270208000000000000 115062030055143074961766298353 35562351837988741246375000000000))
theorem leaf01497_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 108565403122270208000000000000 115062030055143074961766298353 35562351837988741246375000000000 leaf01497_w_raw=true := by decide +kernel
theorem leaf01497_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01497_w_raw=true := by decide +kernel
#print axioms leaf01497_raw
#print axioms leaf01497_rectangular
noncomputable def leaf01497_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01497_w_raw ![12,1,0] ![1,1,1] ![64,2,2])
theorem leaf01497_inner : leaf01497_w_inner=IntegerAffineStages.inner leaf01497_w_raw ![12,1,0] ![1,1,1] ![64,2,2] := by decide +kernel
#print axioms leaf01497_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
