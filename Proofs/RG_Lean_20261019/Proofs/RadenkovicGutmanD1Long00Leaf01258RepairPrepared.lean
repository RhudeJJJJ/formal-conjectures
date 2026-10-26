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
noncomputable def leaf01258_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 306113405613202472960000000000 375847531844394674979959494193 10546763571626946151100000000000))
theorem leaf01258_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 306113405613202472960000000000 375847531844394674979959494193 10546763571626946151100000000000 leaf01258_w_raw=true := by decide +kernel
theorem leaf01258_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01258_w_raw=true := by decide +kernel
#print axioms leaf01258_raw
#print axioms leaf01258_rectangular
noncomputable def leaf01258_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01258_w_raw ![8,0,0] ![1,1,1] ![16,2,1])
theorem leaf01258_inner : leaf01258_w_inner=IntegerAffineStages.inner leaf01258_w_raw ![8,0,0] ![1,1,1] ![16,2,1] := by decide +kernel
#print axioms leaf01258_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
