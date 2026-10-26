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
noncomputable def leaf01436_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 1821550836132610048000000000000 1996574353231235643215635882243 294228048054605168183500000000000))
theorem leaf01436_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 1821550836132610048000000000000 1996574353231235643215635882243 294228048054605168183500000000000 leaf01436_w_raw=true := by decide +kernel
theorem leaf01436_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01436_w_raw=true := by decide +kernel
#print axioms leaf01436_raw
#print axioms leaf01436_rectangular
noncomputable def leaf01436_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01436_w_raw ![16,30,15] ![1,1,1] ![64,32,16])
theorem leaf01436_inner : leaf01436_w_inner=IntegerAffineStages.inner leaf01436_w_raw ![16,30,15] ![1,1,1] ![64,32,16] := by decide +kernel
#print axioms leaf01436_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
