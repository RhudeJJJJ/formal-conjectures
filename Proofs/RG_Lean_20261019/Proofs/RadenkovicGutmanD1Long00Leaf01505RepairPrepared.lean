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
noncomputable def leaf01505_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 1389637086521117900800000000000 1472793905317532348380102027011 455198103047373847407000000000000))
theorem leaf01505_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 1389637086521117900800000000000 1472793905317532348380102027011 455198103047373847407000000000000 leaf01505_w_raw=true := by decide +kernel
theorem leaf01505_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01505_w_raw=true := by decide +kernel
#print axioms leaf01505_raw
#print axioms leaf01505_rectangular
noncomputable def leaf01505_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01505_w_raw ![12,31,30] ![1,1,1] ![64,32,32])
theorem leaf01505_inner : leaf01505_w_inner=IntegerAffineStages.inner leaf01505_w_raw ![12,31,30] ![1,1,1] ![64,32,32] := by decide +kernel
#print axioms leaf01505_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
