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
noncomputable def leaf01512_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 3474092704491634688000000000000 3681984749924019468863171071629 1137995257355148166654500000000000))
theorem leaf01512_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 3474092704491634688000000000000 3681984749924019468863171071629 1137995257355148166654500000000000 leaf01512_w_raw=true := by decide +kernel
theorem leaf01512_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01512_w_raw=true := by decide +kernel
#print axioms leaf01512_raw
#print axioms leaf01512_rectangular
noncomputable def leaf01512_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01512_w_raw ![12,255,255] ![1,1,1] ![64,256,256])
theorem leaf01512_inner : leaf01512_w_inner=IntegerAffineStages.inner leaf01512_w_raw ![12,255,255] ![1,1,1] ![64,256,256] := by decide +kernel
#print axioms leaf01512_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
