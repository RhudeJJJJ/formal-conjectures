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
noncomputable def leaf01309_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 95006123686556073984000000000000 112610320740482266209674811448659 5090804950301137712371000000000000))
theorem leaf01309_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 95006123686556073984000000000000 112610320740482266209674811448659 5090804950301137712371000000000000 leaf01309_w_raw=true := by decide +kernel
theorem leaf01309_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01309_w_raw=true := by decide +kernel
#print axioms leaf01309_raw
#print axioms leaf01309_rectangular
noncomputable def leaf01309_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01309_w_raw ![13,0,0] ![1,1,1] ![32,2,1])
theorem leaf01309_inner : leaf01309_w_inner=IntegerAffineStages.inner leaf01309_w_raw ![13,0,0] ![1,1,1] ![32,2,1] := by decide +kernel
#print axioms leaf01309_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
