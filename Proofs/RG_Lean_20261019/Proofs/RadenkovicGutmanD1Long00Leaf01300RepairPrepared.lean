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
noncomputable def leaf01300_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 4430624910926990540800000000000 5317341782888167821313513473093 206181380895823189631400000000000))
theorem leaf01300_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 4430624910926990540800000000000 5317341782888167821313513473093 206181380895823189631400000000000 leaf01300_w_raw=true := by decide +kernel
theorem leaf01300_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01300_w_raw=true := by decide +kernel
#print axioms leaf01300_raw
#print axioms leaf01300_rectangular
noncomputable def leaf01300_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01300_w_raw ![14,30,15] ![1,1,1] ![32,32,16])
theorem leaf01300_inner : leaf01300_w_inner=IntegerAffineStages.inner leaf01300_w_raw ![14,30,15] ![1,1,1] ![32,32,16] := by decide +kernel
#print axioms leaf01300_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
