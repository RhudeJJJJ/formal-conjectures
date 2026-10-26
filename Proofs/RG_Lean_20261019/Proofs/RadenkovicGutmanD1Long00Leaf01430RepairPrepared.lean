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
noncomputable def leaf01430_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 7286206179208855552000000000000 7986300621189158947466939452739 1176912207134260388955500000000000))
theorem leaf01430_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 7286206179208855552000000000000 7986300621189158947466939452739 1176912207134260388955500000000000 leaf01430_w_raw=true := by decide +kernel
theorem leaf01430_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01430_w_raw=true := by decide +kernel
#print axioms leaf01430_raw
#print axioms leaf01430_rectangular
noncomputable def leaf01430_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01430_w_raw ![16,2,1] ![1,1,1] ![64,4,2])
theorem leaf01430_inner : leaf01430_w_inner=IntegerAffineStages.inner leaf01430_w_raw ![16,2,1] ![1,1,1] ![64,4,2] := by decide +kernel
#print axioms leaf01430_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
