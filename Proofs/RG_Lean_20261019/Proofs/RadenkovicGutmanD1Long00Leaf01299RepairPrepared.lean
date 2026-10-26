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
noncomputable def leaf01299_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 216339868555411456000000000000 259636844804663197651568724603 10067454177385264718062500000000))
theorem leaf01299_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 216339868555411456000000000000 259636844804663197651568724603 10067454177385264718062500000000 leaf01299_w_raw=true := by decide +kernel
theorem leaf01299_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01299_w_raw=true := by decide +kernel
#print axioms leaf01299_raw
#print axioms leaf01299_rectangular
noncomputable def leaf01299_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01299_w_raw ![14,15,14] ![1,1,1] ![32,16,16])
theorem leaf01299_inner : leaf01299_w_inner=IntegerAffineStages.inner leaf01299_w_raw ![14,15,14] ![1,1,1] ![32,16,16] := by decide +kernel
#print axioms leaf01299_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
