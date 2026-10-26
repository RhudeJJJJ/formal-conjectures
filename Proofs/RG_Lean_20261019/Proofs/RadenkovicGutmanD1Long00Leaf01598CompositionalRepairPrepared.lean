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
noncomputable def leaf01598_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 1078568507173502976000000000000 1109589650544372601566046698069 1104624145191531773131000000000000))
theorem leaf01598_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 1078568507173502976000000000000 1109589650544372601566046698069 1104624145191531773131000000000000 leaf01598_w_raw=true := by decide +kernel
theorem leaf01598_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01598_w_raw=true := by decide +kernel
#print axioms leaf01598_raw
#print axioms leaf01598_rectangular
noncomputable def leaf01598_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01598_w_raw ![16,0,0] ![1,1,1] ![128,2,1])
theorem leaf01598_inner : leaf01598_w_inner=IntegerAffineStages.inner leaf01598_w_raw ![16,0,0] ![1,1,1] ![128,2,1] := by decide +kernel
#print axioms leaf01598_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
