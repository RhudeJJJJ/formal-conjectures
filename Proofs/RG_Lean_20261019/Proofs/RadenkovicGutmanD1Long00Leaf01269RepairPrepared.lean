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
noncomputable def leaf01269_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 76506265322107437056000000000000 93932640655298773788784675781397 2636631248060999808201000000000000))
theorem leaf01269_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 76506265322107437056000000000000 93932640655298773788784675781397 2636631248060999808201000000000000 leaf01269_w_raw=true := by decide +kernel
theorem leaf01269_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01269_w_raw=true := by decide +kernel
#print axioms leaf01269_raw
#print axioms leaf01269_rectangular
noncomputable def leaf01269_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01269_w_raw ![8,63,62] ![1,1,1] ![16,64,64])
theorem leaf01269_inner : leaf01269_w_inner=IntegerAffineStages.inner leaf01269_w_raw ![8,63,62] ![1,1,1] ![16,64,64] := by decide +kernel
#print axioms leaf01269_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
