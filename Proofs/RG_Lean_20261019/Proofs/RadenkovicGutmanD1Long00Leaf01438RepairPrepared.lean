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
noncomputable def leaf01438_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 29144812566372941824000000000000 31945188735461648537637284753329 4707648764969576603941000000000000))
theorem leaf01438_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 29144812566372941824000000000000 31945188735461648537637284753329 4707648764969576603941000000000000 leaf01438_w_raw=true := by decide +kernel
theorem leaf01438_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01438_w_raw=true := by decide +kernel
#print axioms leaf01438_raw
#print axioms leaf01438_rectangular
noncomputable def leaf01438_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01438_w_raw ![16,62,31] ![1,1,1] ![64,64,32])
theorem leaf01438_inner : leaf01438_w_inner=IntegerAffineStages.inner leaf01438_w_raw ![16,62,31] ![1,1,1] ![64,64,32] := by decide +kernel
#print axioms leaf01438_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
