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
noncomputable def leaf01268_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 153012813734099288064000000000000 187865638366523112725439232899519 5273262762349720286291000000000000))
theorem leaf01268_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 153012813734099288064000000000000 187865638366523112725439232899519 5273262762349720286291000000000000 leaf01268_w_raw=true := by decide +kernel
theorem leaf01268_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01268_w_raw=true := by decide +kernel
#print axioms leaf01268_raw
#print axioms leaf01268_rectangular
noncomputable def leaf01268_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01268_w_raw ![8,62,31] ![1,1,1] ![16,64,32])
theorem leaf01268_inner : leaf01268_w_inner=IntegerAffineStages.inner leaf01268_w_raw ![8,62,31] ![1,1,1] ![16,64,32] := by decide +kernel
#print axioms leaf01268_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
