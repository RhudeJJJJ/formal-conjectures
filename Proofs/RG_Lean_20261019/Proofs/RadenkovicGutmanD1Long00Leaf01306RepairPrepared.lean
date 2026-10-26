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
noncomputable def leaf01306_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 36056332725387264000000000000 43272399311429296291794590679 1677907723855793798781250000000))
theorem leaf01306_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 36056332725387264000000000000 43272399311429296291794590679 1677907723855793798781250000000 leaf01306_w_raw=true := by decide +kernel
theorem leaf01306_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01306_w_raw=true := by decide +kernel
#print axioms leaf01306_raw
#print axioms leaf01306_rectangular
noncomputable def leaf01306_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01306_w_raw ![14,254,127] ![1,1,1] ![32,256,128])
theorem leaf01306_inner : leaf01306_w_inner=IntegerAffineStages.inner leaf01306_w_raw ![14,254,127] ![1,1,1] ![32,256,128] := by decide +kernel
#print axioms leaf01306_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
