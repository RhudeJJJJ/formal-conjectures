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
noncomputable def leaf01407_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 609590865425334272000000000000 679580555077317747615524637963 74813914765450601424750000000000))
theorem leaf01407_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 609590865425334272000000000000 679580555077317747615524637963 74813914765450601424750000000000 leaf01407_w_raw=true := by decide +kernel
theorem leaf01407_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01407_w_raw=true := by decide +kernel
#print axioms leaf01407_raw
#print axioms leaf01407_rectangular
noncomputable def leaf01407_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01407_w_raw ![18,127,126] ![1,1,1] ![64,128,128])
theorem leaf01407_inner : leaf01407_w_inner=IntegerAffineStages.inner leaf01407_w_raw ![18,127,126] ![1,1,1] ![64,128,128] := by decide +kernel
#print axioms leaf01407_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
