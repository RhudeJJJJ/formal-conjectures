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
noncomputable def leaf01329_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 8007778306328677580800000000000 9362768064518929732412190975241 502171527468002008717000000000000))
theorem leaf01329_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 8007778306328677580800000000000 9362768064518929732412190975241 502171527468002008717000000000000 leaf01329_w_raw=true := by decide +kernel
theorem leaf01329_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01329_w_raw=true := by decide +kernel
#print axioms leaf01329_raw
#print axioms leaf01329_rectangular
noncomputable def leaf01329_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01329_w_raw ![12,3,2] ![1,1,1] ![32,4,4])
theorem leaf01329_inner : leaf01329_w_inner=IntegerAffineStages.inner leaf01329_w_raw ![12,3,2] ![1,1,1] ![32,4,4] := by decide +kernel
#print axioms leaf01329_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
