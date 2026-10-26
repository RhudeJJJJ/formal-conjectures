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
noncomputable def leaf01678_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 4816675846016204800000000000 4897085356091602382550197181 10916668529567884087800000000000))
theorem leaf01678_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 4816675846016204800000000000 4897085356091602382550197181 10916668529567884087800000000000 leaf01678_w_raw=true := by decide +kernel
theorem leaf01678_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01678_w_raw=true := by decide +kernel
#print axioms leaf01678_raw
#print axioms leaf01678_rectangular
noncomputable def leaf01678_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01678_w_raw ![12,126,63] ![1,1,1] ![128,128,64])
theorem leaf01678_inner : leaf01678_w_inner=IntegerAffineStages.inner leaf01678_w_raw ![12,126,63] ![1,1,1] ![128,128,64] := by decide +kernel
#print axioms leaf01678_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
