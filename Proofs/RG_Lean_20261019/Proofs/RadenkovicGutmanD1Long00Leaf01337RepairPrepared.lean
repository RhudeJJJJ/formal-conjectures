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
noncomputable def leaf01337_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 40038442952374091776000000000000 46813279385283264074018462562639 2510855682093658929897000000000000))
theorem leaf01337_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 40038442952374091776000000000000 46813279385283264074018462562639 2510855682093658929897000000000000 leaf01337_w_raw=true := by decide +kernel
theorem leaf01337_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01337_w_raw=true := by decide +kernel
#print axioms leaf01337_raw
#print axioms leaf01337_rectangular
noncomputable def leaf01337_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01337_w_raw ![12,63,62] ![1,1,1] ![32,64,64])
theorem leaf01337_inner : leaf01337_w_inner=IntegerAffineStages.inner leaf01337_w_raw ![12,63,62] ![1,1,1] ![32,64,64] := by decide +kernel
#print axioms leaf01337_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
