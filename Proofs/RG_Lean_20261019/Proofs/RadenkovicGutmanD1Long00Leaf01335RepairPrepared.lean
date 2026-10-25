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
noncomputable def leaf01335_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 100096182140209725440000000000 117033291935346859730909678357 6277139530424878004750000000000))
theorem leaf01335_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 100096182140209725440000000000 117033291935346859730909678357 6277139530424878004750000000000 leaf01335_w_raw=true := by decide +kernel
theorem leaf01335_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01335_w_raw=true := by decide +kernel
#print axioms leaf01335_raw
#print axioms leaf01335_rectangular
noncomputable def leaf01335_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01335_w_raw ![12,31,30] ![1,1,1] ![32,32,32])
theorem leaf01335_inner : leaf01335_w_inner=IntegerAffineStages.inner leaf01335_w_raw ![12,31,30] ![1,1,1] ![32,32,32] := by decide +kernel
#print axioms leaf01335_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
