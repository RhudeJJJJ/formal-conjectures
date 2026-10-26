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
noncomputable def leaf01435_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 1821550896799023104000000000000 1996574423163894736728080431059 294228048561121312607250000000000))
theorem leaf01435_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 1821550896799023104000000000000 1996574423163894736728080431059 294228048561121312607250000000000 leaf01435_w_raw=true := by decide +kernel
theorem leaf01435_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01435_w_raw=true := by decide +kernel
#print axioms leaf01435_raw
#print axioms leaf01435_rectangular
noncomputable def leaf01435_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01435_w_raw ![16,15,14] ![1,1,1] ![64,16,16])
theorem leaf01435_inner : leaf01435_w_inner=IntegerAffineStages.inner leaf01435_w_raw ![16,15,14] ![1,1,1] ![64,16,16] := by decide +kernel
#print axioms leaf01435_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
