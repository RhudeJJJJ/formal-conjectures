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
noncomputable def leaf01336_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 104266797988970496000000000000 121909604836089523381719452937 6538686690484392235562500000000))
theorem leaf01336_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 104266797988970496000000000000 121909604836089523381719452937 6538686690484392235562500000000 leaf01336_w_raw=true := by decide +kernel
theorem leaf01336_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01336_w_raw=true := by decide +kernel
#print axioms leaf01336_raw
#print axioms leaf01336_rectangular
noncomputable def leaf01336_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01336_w_raw ![12,62,31] ![1,1,1] ![32,64,32])
theorem leaf01336_inner : leaf01336_w_inner=IntegerAffineStages.inner leaf01336_w_raw ![12,62,31] ![1,1,1] ![32,64,32] := by decide +kernel
#print axioms leaf01336_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
