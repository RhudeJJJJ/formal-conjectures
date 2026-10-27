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
noncomputable def leaf01446_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 96722652030304256000000000000 105116059488908551652860704237 18233110839038279438250000000000))
theorem leaf01446_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 96722652030304256000000000000 105116059488908551652860704237 18233110839038279438250000000000 leaf01446_w_raw=true := by decide +kernel
theorem leaf01446_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01446_w_raw=true := by decide +kernel
#print axioms leaf01446_raw
#print axioms leaf01446_rectangular
noncomputable def leaf01446_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01446_w_raw ![15,1,0] ![1,1,1] ![64,2,2])
theorem leaf01446_inner : leaf01446_w_inner=IntegerAffineStages.inner leaf01446_w_raw ![15,1,0] ![1,1,1] ![64,2,2] := by decide +kernel
#print axioms leaf01446_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
