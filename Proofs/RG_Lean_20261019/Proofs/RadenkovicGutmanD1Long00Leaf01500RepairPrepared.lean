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
noncomputable def leaf01500_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 13896371062779674624000000000000 14727939266487720642829837971351 4551981031685689802229000000000000))
theorem leaf01500_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 13896371062779674624000000000000 14727939266487720642829837971351 4551981031685689802229000000000000 leaf01500_w_raw=true := by decide +kernel
theorem leaf01500_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01500_w_raw=true := by decide +kernel
#print axioms leaf01500_raw
#print axioms leaf01500_rectangular
noncomputable def leaf01500_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01500_w_raw ![12,6,3] ![1,1,1] ![64,8,4])
theorem leaf01500_inner : leaf01500_w_inner=IntegerAffineStages.inner leaf01500_w_raw ![12,6,3] ![1,1,1] ![64,8,4] := by decide +kernel
#print axioms leaf01500_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
