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
noncomputable def leaf01277_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 3976498791950843904000000000000 4826062694994544380320832564507 162892837140771824749000000000000))
theorem leaf01277_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 3976498791950843904000000000000 4826062694994544380320832564507 162892837140771824749000000000000 leaf01277_w_raw=true := by decide +kernel
theorem leaf01277_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01277_w_raw=true := by decide +kernel
#print axioms leaf01277_raw
#print axioms leaf01277_rectangular
noncomputable def leaf01277_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01277_w_raw ![15,2,1] ![1,1,1] ![32,4,2])
theorem leaf01277_inner : leaf01277_w_inner=IntegerAffineStages.inner leaf01277_w_raw ![15,2,1] ![1,1,1] ![32,4,2] := by decide +kernel
#print axioms leaf01277_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
