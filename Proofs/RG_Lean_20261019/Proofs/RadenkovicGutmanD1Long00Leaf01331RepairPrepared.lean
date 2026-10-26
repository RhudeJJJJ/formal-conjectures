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
noncomputable def leaf01331_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 80077304578160197632000000000000 93627082297241776486961543003109 5021713188336101969627000000000000))
theorem leaf01331_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 80077304578160197632000000000000 93627082297241776486961543003109 5021713188336101969627000000000000 leaf01331_w_raw=true := by decide +kernel
theorem leaf01331_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01331_w_raw=true := by decide +kernel
#print axioms leaf01331_raw
#print axioms leaf01331_rectangular
noncomputable def leaf01331_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01331_w_raw ![12,7,6] ![1,1,1] ![32,8,8])
theorem leaf01331_inner : leaf01331_w_inner=IntegerAffineStages.inner leaf01331_w_raw ![12,7,6] ![1,1,1] ![32,8,8] := by decide +kernel
#print axioms leaf01331_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
