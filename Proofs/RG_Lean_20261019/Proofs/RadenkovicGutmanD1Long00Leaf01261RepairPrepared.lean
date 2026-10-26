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
noncomputable def leaf01261_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 15302951768225218560000000000 18788804741095136996768315817 527331609719190431470000000000))
theorem leaf01261_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 15302951768225218560000000000 18788804741095136996768315817 527331609719190431470000000000 leaf01261_w_raw=true := by decide +kernel
theorem leaf01261_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01261_w_raw=true := by decide +kernel
#print axioms leaf01261_raw
#print axioms leaf01261_rectangular
noncomputable def leaf01261_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01261_w_raw ![8,3,2] ![1,1,1] ![16,4,4])
theorem leaf01261_inner : leaf01261_w_inner=IntegerAffineStages.inner leaf01261_w_raw ![8,3,2] ![1,1,1] ![16,4,4] := by decide +kernel
#print axioms leaf01261_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
