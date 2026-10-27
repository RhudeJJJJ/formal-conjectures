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
noncomputable def leaf01401_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 2438363980855508992000000000000 2718322827194941395070081036597 299255662158061974158500000000000))
theorem leaf01401_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 2438363980855508992000000000000 2718322827194941395070081036597 299255662158061974158500000000000 leaf01401_w_raw=true := by decide +kernel
theorem leaf01401_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01401_w_raw=true := by decide +kernel
#print axioms leaf01401_raw
#print axioms leaf01401_rectangular
noncomputable def leaf01401_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01401_w_raw ![18,15,14] ![1,1,1] ![64,16,16])
theorem leaf01401_inner : leaf01401_w_inner=IntegerAffineStages.inner leaf01401_w_raw ![18,15,14] ![1,1,1] ![64,16,16] := by decide +kernel
#print axioms leaf01401_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
