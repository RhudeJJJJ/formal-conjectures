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
noncomputable def leaf01448_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 198087951122809487360000000000 215277644603402688014224290457 37341410737628983666600000000000))
theorem leaf01448_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 198087951122809487360000000000 215277644603402688014224290457 37341410737628983666600000000000 leaf01448_w_raw=true := by decide +kernel
theorem leaf01448_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01448_w_raw=true := by decide +kernel
#print axioms leaf01448_raw
#print axioms leaf01448_rectangular
noncomputable def leaf01448_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01448_w_raw ![15,3,2] ![1,1,1] ![64,4,4])
theorem leaf01448_inner : leaf01448_w_inner=IntegerAffineStages.inner leaf01448_w_raw ![15,3,2] ![1,1,1] ![64,4,4] := by decide +kernel
#print axioms leaf01448_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
