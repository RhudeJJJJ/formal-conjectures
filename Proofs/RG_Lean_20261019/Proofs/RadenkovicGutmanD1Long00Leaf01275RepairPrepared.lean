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
noncomputable def leaf01275_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 5090309187831437721600000000000 6177874034177980125819631850109 208504167086996675536600000000000))
theorem leaf01275_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 5090309187831437721600000000000 6177874034177980125819631850109 208504167086996675536600000000000 leaf01275_w_raw=true := by decide +kernel
theorem leaf01275_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01275_w_raw=true := by decide +kernel
#print axioms leaf01275_raw
#print axioms leaf01275_rectangular
noncomputable def leaf01275_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01275_w_raw ![15,0,0] ![1,1,1] ![32,2,1])
theorem leaf01275_inner : leaf01275_w_inner=IntegerAffineStages.inner leaf01275_w_raw ![15,0,0] ![1,1,1] ![32,2,1] := by decide +kernel
#print axioms leaf01275_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
