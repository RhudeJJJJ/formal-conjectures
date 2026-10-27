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
noncomputable def leaf01507_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 1389637083944137523200000000000 1472793902577535465827950140251 455198103044651467053000000000000))
theorem leaf01507_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 1389637083944137523200000000000 1472793902577535465827950140251 455198103044651467053000000000000 leaf01507_w_raw=true := by decide +kernel
theorem leaf01507_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01507_w_raw=true := by decide +kernel
#print axioms leaf01507_raw
#print axioms leaf01507_rectangular
noncomputable def leaf01507_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01507_w_raw ![12,63,62] ![1,1,1] ![64,64,64])
theorem leaf01507_inner : leaf01507_w_inner=IntegerAffineStages.inner leaf01507_w_raw ![12,63,62] ![1,1,1] ![64,64,64] := by decide +kernel
#print axioms leaf01507_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
