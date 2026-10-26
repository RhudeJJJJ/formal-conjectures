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
noncomputable def leaf01439_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 455387693866549248000000000000 499143571251634981707655453449 73557011949946368828875000000000))
theorem leaf01439_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 455387693866549248000000000000 499143571251634981707655453449 73557011949946368828875000000000 leaf01439_w_raw=true := by decide +kernel
theorem leaf01439_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01439_w_raw=true := by decide +kernel
#print axioms leaf01439_raw
#print axioms leaf01439_rectangular
noncomputable def leaf01439_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01439_w_raw ![16,63,62] ![1,1,1] ![64,64,64])
theorem leaf01439_inner : leaf01439_w_inner=IntegerAffineStages.inner leaf01439_w_raw ![16,63,62] ![1,1,1] ![64,64,64] := by decide +kernel
#print axioms leaf01439_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
