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
noncomputable def leaf01326_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 1112211368792031232000000000000 1300408962857363670139303093503 69746109762538218497000000000000))
theorem leaf01326_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 1112211368792031232000000000000 1300408962857363670139303093503 69746109762538218497000000000000 leaf01326_w_raw=true := by decide +kernel
theorem leaf01326_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01326_w_raw=true := by decide +kernel
#print axioms leaf01326_raw
#print axioms leaf01326_rectangular
noncomputable def leaf01326_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01326_w_raw ![12,0,0] ![1,1,1] ![32,2,1])
theorem leaf01326_inner : leaf01326_w_inner=IntegerAffineStages.inner leaf01326_w_raw ![12,0,0] ![1,1,1] ![32,2,1] := by decide +kernel
#print axioms leaf01326_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
