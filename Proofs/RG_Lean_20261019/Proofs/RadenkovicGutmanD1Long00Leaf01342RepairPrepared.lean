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
noncomputable def leaf01342_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 156400065567522816000000000000 182864243852704428321833010849 9808029512842380599500000000000))
theorem leaf01342_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 156400065567522816000000000000 182864243852704428321833010849 9808029512842380599500000000000 leaf01342_w_raw=true := by decide +kernel
theorem leaf01342_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01342_w_raw=true := by decide +kernel
#print axioms leaf01342_raw
#print axioms leaf01342_rectangular
noncomputable def leaf01342_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01342_w_raw ![12,255,255] ![1,1,1] ![32,256,256])
theorem leaf01342_inner : leaf01342_w_inner=IntegerAffineStages.inner leaf01342_w_raw ![12,255,255] ![1,1,1] ![32,256,256] := by decide +kernel
#print axioms leaf01342_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
