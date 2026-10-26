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
noncomputable def leaf01303_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 55382616425136914432000000000000 66466522754622243246934048204261 2577266658174471012079000000000000))
theorem leaf01303_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 55382616425136914432000000000000 66466522754622243246934048204261 2577266658174471012079000000000000 leaf01303_w_raw=true := by decide +kernel
theorem leaf01303_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01303_w_raw=true := by decide +kernel
#print axioms leaf01303_raw
#print axioms leaf01303_rectangular
noncomputable def leaf01303_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01303_w_raw ![14,63,62] ![1,1,1] ![32,64,64])
theorem leaf01303_inner : leaf01303_w_inner=IntegerAffineStages.inner leaf01303_w_raw ![14,63,62] ![1,1,1] ![32,64,64] := by decide +kernel
#print axioms leaf01303_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
