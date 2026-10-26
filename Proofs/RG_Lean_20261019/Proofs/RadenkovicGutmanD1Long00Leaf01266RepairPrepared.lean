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
noncomputable def leaf01266_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 19126778650624524288000000000000 23483439129398850953542126778367 659158325225099352495500000000000))
theorem leaf01266_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 19126778650624524288000000000000 23483439129398850953542126778367 659158325225099352495500000000000 leaf01266_w_raw=true := by decide +kernel
theorem leaf01266_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01266_w_raw=true := by decide +kernel
#print axioms leaf01266_raw
#print axioms leaf01266_rectangular
noncomputable def leaf01266_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01266_w_raw ![8,30,15] ![1,1,1] ![16,32,16])
theorem leaf01266_inner : leaf01266_w_inner=IntegerAffineStages.inner leaf01266_w_raw ![8,30,15] ![1,1,1] ![16,32,16] := by decide +kernel
#print axioms leaf01266_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
