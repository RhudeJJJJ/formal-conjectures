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
noncomputable def leaf01305_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 110765102875973517312000000000000 132932875680602020969215283353483 5154532779613069941439000000000000))
theorem leaf01305_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 110765102875973517312000000000000 132932875680602020969215283353483 5154532779613069941439000000000000 leaf01305_w_raw=true := by decide +kernel
theorem leaf01305_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01305_w_raw=true := by decide +kernel
#print axioms leaf01305_raw
#print axioms leaf01305_rectangular
noncomputable def leaf01305_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01305_w_raw ![14,127,126] ![1,1,1] ![32,128,128])
theorem leaf01305_inner : leaf01305_w_inner=IntegerAffineStages.inner leaf01305_w_raw ![14,127,126] ![1,1,1] ![32,128,128] := by decide +kernel
#print axioms leaf01305_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
