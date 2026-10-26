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
noncomputable def leaf01272_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 8500652897057374208000000000000 10436901799799667186283764036573 292958882391128780607000000000000))
theorem leaf01272_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 8500652897057374208000000000000 10436901799799667186283764036573 292958882391128780607000000000000 leaf01272_w_raw=true := by decide +kernel
theorem leaf01272_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01272_w_raw=true := by decide +kernel
#print axioms leaf01272_raw
#print axioms leaf01272_rectangular
noncomputable def leaf01272_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01272_w_raw ![8,254,127] ![1,1,1] ![16,256,128])
theorem leaf01272_inner : leaf01272_w_inner=IntegerAffineStages.inner leaf01272_w_raw ![8,254,127] ![1,1,1] ![16,256,128] := by decide +kernel
#print axioms leaf01272_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
