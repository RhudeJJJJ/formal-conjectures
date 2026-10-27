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
noncomputable def leaf01348_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 516630760237563904000000000000 595178001172076250369210886179 38655963417743634272625000000000))
theorem leaf01348_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 516630760237563904000000000000 595178001172076250369210886179 38655963417743634272625000000000 leaf01348_w_raw=true := by decide +kernel
theorem leaf01348_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01348_w_raw=true := by decide +kernel
#print axioms leaf01348_raw
#print axioms leaf01348_rectangular
noncomputable def leaf01348_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01348_w_raw ![11,7,6] ![1,1,1] ![32,8,8])
theorem leaf01348_inner : leaf01348_w_inner=IntegerAffineStages.inner leaf01348_w_raw ![11,7,6] ![1,1,1] ![32,8,8] := by decide +kernel
#print axioms leaf01348_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
