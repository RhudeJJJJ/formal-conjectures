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
noncomputable def leaf01276_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 7953363894414606336000000000000 9652624313664924983667449725533 325787508736395508861750000000000))
theorem leaf01276_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 7953363894414606336000000000000 9652624313664924983667449725533 325787508736395508861750000000000 leaf01276_w_raw=true := by decide +kernel
theorem leaf01276_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01276_w_raw=true := by decide +kernel
#print axioms leaf01276_raw
#print axioms leaf01276_rectangular
noncomputable def leaf01276_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01276_w_raw ![15,1,0] ![1,1,1] ![32,2,2])
theorem leaf01276_inner : leaf01276_w_inner=IntegerAffineStages.inner leaf01276_w_raw ![15,1,0] ![1,1,1] ![32,2,2] := by decide +kernel
#print axioms leaf01276_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
