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
noncomputable def leaf01516_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 88341336678077562880000000000 92883662758131227108755109187 36126443984664247498200000000000))
theorem leaf01516_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 88341336678077562880000000000 92883662758131227108755109187 36126443984664247498200000000000 leaf01516_w_raw=true := by decide +kernel
theorem leaf01516_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01516_w_raw=true := by decide +kernel
#print axioms leaf01516_raw
#print axioms leaf01516_rectangular
noncomputable def leaf01516_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01516_w_raw ![11,3,2] ![1,1,1] ![64,4,4])
theorem leaf01516_inner : leaf01516_w_inner=IntegerAffineStages.inner leaf01516_w_raw ![11,3,2] ![1,1,1] ![64,4,4] := by decide +kernel
#print axioms leaf01516_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
