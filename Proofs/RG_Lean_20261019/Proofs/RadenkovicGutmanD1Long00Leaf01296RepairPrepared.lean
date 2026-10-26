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
noncomputable def leaf01296_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 5408572872379596800000000000 6491018591706505141909135427 251686589842420938546875000000))
theorem leaf01296_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 5408572872379596800000000000 6491018591706505141909135427 251686589842420938546875000000 leaf01296_w_raw=true := by decide +kernel
theorem leaf01296_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01296_w_raw=true := by decide +kernel
#print axioms leaf01296_raw
#print axioms leaf01296_rectangular
noncomputable def leaf01296_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01296_w_raw ![14,6,3] ![1,1,1] ![32,8,4])
theorem leaf01296_inner : leaf01296_w_inner=IntegerAffineStages.inner leaf01296_w_raw ![14,6,3] ![1,1,1] ![32,8,4] := by decide +kernel
#print axioms leaf01296_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
