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
noncomputable def leaf01619_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 3602654718624530432000000000000 3694496663569447782977880576207 4404458263285939085871000000000000))
theorem leaf01619_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 3602654718624530432000000000000 3694496663569447782977880576207 4404458263285939085871000000000000 leaf01619_w_raw=true := by decide +kernel
theorem leaf01619_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01619_w_raw=true := by decide +kernel
#print axioms leaf01619_raw
#print axioms leaf01619_rectangular
noncomputable def leaf01619_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01619_w_raw ![15,6,3] ![1,1,1] ![128,8,4])
theorem leaf01619_inner : leaf01619_w_inner=IntegerAffineStages.inner leaf01619_w_raw ![15,6,3] ![1,1,1] ![128,8,4] := by decide +kernel
#print axioms leaf01619_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
