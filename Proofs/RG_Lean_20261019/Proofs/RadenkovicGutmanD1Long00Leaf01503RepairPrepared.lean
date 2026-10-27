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
noncomputable def leaf01503_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 7237693183570739200000000000 7670801616358645658735562537 2370823453397733739875000000000))
theorem leaf01503_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 7237693183570739200000000000 7670801616358645658735562537 2370823453397733739875000000000 leaf01503_w_raw=true := by decide +kernel
theorem leaf01503_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01503_w_raw=true := by decide +kernel
#print axioms leaf01503_raw
#print axioms leaf01503_rectangular
noncomputable def leaf01503_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01503_w_raw ![12,15,14] ![1,1,1] ![64,16,16])
theorem leaf01503_inner : leaf01503_w_inner=IntegerAffineStages.inner leaf01503_w_raw ![12,15,14] ![1,1,1] ![64,16,16] := by decide +kernel
#print axioms leaf01503_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
