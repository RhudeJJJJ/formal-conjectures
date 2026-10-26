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
noncomputable def leaf01302_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 23076103716129996800000000000 27694401083079876915529707819 1073861121275718614100000000000))
theorem leaf01302_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 23076103716129996800000000000 27694401083079876915529707819 1073861121275718614100000000000 leaf01302_w_raw=true := by decide +kernel
theorem leaf01302_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01302_w_raw=true := by decide +kernel
#print axioms leaf01302_raw
#print axioms leaf01302_rectangular
noncomputable def leaf01302_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01302_w_raw ![14,62,31] ![1,1,1] ![32,64,32])
theorem leaf01302_inner : leaf01302_w_inner=IntegerAffineStages.inner leaf01302_w_raw ![14,62,31] ![1,1,1] ![32,64,32] := by decide +kernel
#print axioms leaf01302_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
