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
noncomputable def leaf01515_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 552133356170720051200000000000 580522894275643950972689386467 225790274906178448030500000000000))
theorem leaf01515_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 552133356170720051200000000000 580522894275643950972689386467 225790274906178448030500000000000 leaf01515_w_raw=true := by decide +kernel
theorem leaf01515_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01515_w_raw=true := by decide +kernel
#print axioms leaf01515_raw
#print axioms leaf01515_rectangular
noncomputable def leaf01515_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01515_w_raw ![11,2,1] ![1,1,1] ![64,4,2])
theorem leaf01515_inner : leaf01515_w_inner=IntegerAffineStages.inner leaf01515_w_raw ![11,2,1] ![1,1,1] ![64,4,2] := by decide +kernel
#print axioms leaf01515_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
