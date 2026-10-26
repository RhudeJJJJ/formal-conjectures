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
noncomputable def leaf01259_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 19130955078970638336000000000000 23489042012262591591320844232641 659171659495018727909500000000000))
theorem leaf01259_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 19130955078970638336000000000000 23489042012262591591320844232641 659171659495018727909500000000000 leaf01259_w_raw=true := by decide +kernel
theorem leaf01259_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01259_w_raw=true := by decide +kernel
#print axioms leaf01259_raw
#print axioms leaf01259_rectangular
noncomputable def leaf01259_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01259_w_raw ![8,1,0] ![1,1,1] ![16,2,2])
theorem leaf01259_inner : leaf01259_w_inner=IntegerAffineStages.inner leaf01259_w_raw ![8,1,0] ![1,1,1] ![16,2,2] := by decide +kernel
#print axioms leaf01259_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
