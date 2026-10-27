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
noncomputable def leaf01345_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 66129040178616991744000000000000 76183148377649933294308256733439 4947964311965384953051000000000000))
theorem leaf01345_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 66129040178616991744000000000000 76183148377649933294308256733439 4947964311965384953051000000000000 leaf01345_w_raw=true := by decide +kernel
theorem leaf01345_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01345_w_raw=true := by decide +kernel
#print axioms leaf01345_raw
#print axioms leaf01345_rectangular
noncomputable def leaf01345_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01345_w_raw ![11,2,1] ![1,1,1] ![32,4,2])
theorem leaf01345_inner : leaf01345_w_inner=IntegerAffineStages.inner leaf01345_w_raw ![11,2,1] ![1,1,1] ![32,4,2] := by decide +kernel
#print axioms leaf01345_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
