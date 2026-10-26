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
noncomputable def leaf01273_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 153011681374561632256000000000000 187864143141697776371807763692371 5273259816742316811511000000000000))
theorem leaf01273_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 153011681374561632256000000000000 187864143141697776371807763692371 5273259816742316811511000000000000 leaf01273_w_raw=true := by decide +kernel
theorem leaf01273_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01273_w_raw=true := by decide +kernel
#print axioms leaf01273_raw
#print axioms leaf01273_rectangular
noncomputable def leaf01273_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01273_w_raw ![8,255,254] ![1,1,1] ![16,256,256])
theorem leaf01273_inner : leaf01273_w_inner=IntegerAffineStages.inner leaf01273_w_raw ![8,255,254] ![1,1,1] ![16,256,256] := by decide +kernel
#print axioms leaf01273_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
