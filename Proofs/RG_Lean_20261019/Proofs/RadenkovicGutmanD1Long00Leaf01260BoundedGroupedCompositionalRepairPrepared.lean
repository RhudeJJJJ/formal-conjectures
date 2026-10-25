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
noncomputable def leaf01260_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 95646279954910412800000000000 117433600742788206146848872291 3295825219754812282575000000000))
theorem leaf01260_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 95646279954910412800000000000 117433600742788206146848872291 3295825219754812282575000000000 leaf01260_w_raw=true := by decide +kernel
theorem leaf01260_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01260_w_raw=true := by decide +kernel
#print axioms leaf01260_raw
#print axioms leaf01260_rectangular
noncomputable def leaf01260_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01260_w_raw ![8,2,1] ![1,1,1] ![16,4,2])
theorem leaf01260_inner : leaf01260_w_inner=IntegerAffineStages.inner leaf01260_w_raw ![8,2,1] ![1,1,1] ![16,4,2] := by decide +kernel
#print axioms leaf01260_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
