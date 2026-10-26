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
noncomputable def leaf01271_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 51003988154815348736000000000000 62621507506304136899192294817327 1757753569841199385499000000000000))
theorem leaf01271_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 51003988154815348736000000000000 62621507506304136899192294817327 1757753569841199385499000000000000 leaf01271_w_raw=true := by decide +kernel
theorem leaf01271_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01271_w_raw=true := by decide +kernel
#print axioms leaf01271_raw
#print axioms leaf01271_rectangular
noncomputable def leaf01271_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01271_w_raw ![8,127,126] ![1,1,1] ![16,128,128])
theorem leaf01271_inner : leaf01271_w_inner=IntegerAffineStages.inner leaf01271_w_raw ![8,127,126] ![1,1,1] ![16,128,128] := by decide +kernel
#print axioms leaf01271_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
