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
noncomputable def leaf01294_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 1730783938277801984000000000000 2077178372242471977008619093291 80539851222138679489125000000000))
theorem leaf01294_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 1730783938277801984000000000000 2077178372242471977008619093291 80539851222138679489125000000000 leaf01294_w_raw=true := by decide +kernel
theorem leaf01294_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01294_w_raw=true := by decide +kernel
#print axioms leaf01294_raw
#print axioms leaf01294_rectangular
noncomputable def leaf01294_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01294_w_raw ![14,2,1] ![1,1,1] ![32,4,2])
theorem leaf01294_inner : leaf01294_w_inner=IntegerAffineStages.inner leaf01294_w_raw ![14,2,1] ![1,1,1] ![32,4,2] := by decide +kernel
#print axioms leaf01294_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
