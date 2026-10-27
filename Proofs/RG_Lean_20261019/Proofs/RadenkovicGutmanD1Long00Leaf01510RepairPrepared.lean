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
noncomputable def leaf01510_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 13896370822261506048000000000000 14727939004262739345298406920341 4551981029425129967207000000000000))
theorem leaf01510_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 13896370822261506048000000000000 14727939004262739345298406920341 4551981029425129967207000000000000 leaf01510_w_raw=true := by decide +kernel
theorem leaf01510_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01510_w_raw=true := by decide +kernel
#print axioms leaf01510_raw
#print axioms leaf01510_rectangular
noncomputable def leaf01510_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01510_w_raw ![12,254,127] ![1,1,1] ![64,256,128])
theorem leaf01510_inner : leaf01510_w_inner=IntegerAffineStages.inner leaf01510_w_raw ![12,254,127] ![1,1,1] ![64,256,128] := by decide +kernel
#print axioms leaf01510_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
