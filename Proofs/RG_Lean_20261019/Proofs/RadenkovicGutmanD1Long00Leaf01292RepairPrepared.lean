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
noncomputable def leaf01292_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 295400990868913520640000000000 354523003409285597413477621503 13745516568004313466200000000000))
theorem leaf01292_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 295400990868913520640000000000 354523003409285597413477621503 13745516568004313466200000000000 leaf01292_w_raw=true := by decide +kernel
theorem leaf01292_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01292_w_raw=true := by decide +kernel
#print axioms leaf01292_raw
#print axioms leaf01292_rectangular
noncomputable def leaf01292_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01292_w_raw ![14,0,0] ![1,1,1] ![32,2,1])
theorem leaf01292_inner : leaf01292_w_inner=IntegerAffineStages.inner leaf01292_w_raw ![14,0,0] ![1,1,1] ![32,2,1] := by decide +kernel
#print axioms leaf01292_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
