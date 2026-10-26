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
noncomputable def leaf01518_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 2208533403208043724800000000000 2322091554465644898218096041643 903161099602192668047000000000000))
theorem leaf01518_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 2208533403208043724800000000000 2322091554465644898218096041643 903161099602192668047000000000000 leaf01518_w_raw=true := by decide +kernel
theorem leaf01518_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01518_w_raw=true := by decide +kernel
#print axioms leaf01518_raw
#print axioms leaf01518_rectangular
noncomputable def leaf01518_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01518_w_raw ![11,7,6] ![1,1,1] ![64,8,8])
theorem leaf01518_inner : leaf01518_w_inner=IntegerAffineStages.inner leaf01518_w_raw ![11,7,6] ![1,1,1] ![64,8,8] := by decide +kernel
#print axioms leaf01518_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
