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
noncomputable def leaf01437_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 1821550815731515392000000000000 1996574330719187077603657038363 294228048032394553446500000000000))
theorem leaf01437_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 1821550815731515392000000000000 1996574330719187077603657038363 294228048032394553446500000000000 leaf01437_w_raw=true := by decide +kernel
theorem leaf01437_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01437_w_raw=true := by decide +kernel
#print axioms leaf01437_raw
#print axioms leaf01437_rectangular
noncomputable def leaf01437_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01437_w_raw ![16,31,30] ![1,1,1] ![64,32,32])
theorem leaf01437_inner : leaf01437_w_inner=IntegerAffineStages.inner leaf01437_w_raw ![16,31,30] ![1,1,1] ![64,32,32] := by decide +kernel
#print axioms leaf01437_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
