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
noncomputable def leaf01265_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 19126990975017156608000000000000 23483729271124593213274135398171 659159151976253112069000000000000))
theorem leaf01265_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 19126990975017156608000000000000 23483729271124593213274135398171 659159151976253112069000000000000 leaf01265_w_raw=true := by decide +kernel
theorem leaf01265_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01265_w_raw=true := by decide +kernel
#print axioms leaf01265_raw
#print axioms leaf01265_rectangular
noncomputable def leaf01265_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01265_w_raw ![8,15,14] ![1,1,1] ![16,16,16])
theorem leaf01265_inner : leaf01265_w_inner=IntegerAffineStages.inner leaf01265_w_raw ![8,15,14] ![1,1,1] ![16,16,16] := by decide +kernel
#print axioms leaf01265_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
