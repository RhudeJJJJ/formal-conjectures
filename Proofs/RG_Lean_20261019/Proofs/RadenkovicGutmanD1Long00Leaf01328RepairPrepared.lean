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
noncomputable def leaf01328_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 16015604462029006438400000000000 18725592928031618373587580376721 1004343100690132671773000000000000))
theorem leaf01328_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 16015604462029006438400000000000 18725592928031618373587580376721 1004343100690132671773000000000000 leaf01328_w_raw=true := by decide +kernel
theorem leaf01328_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01328_w_raw=true := by decide +kernel
#print axioms leaf01328_raw
#print axioms leaf01328_rectangular
noncomputable def leaf01328_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01328_w_raw ![12,2,1] ![1,1,1] ![32,4,2])
theorem leaf01328_inner : leaf01328_w_inner=IntegerAffineStages.inner leaf01328_w_raw ![12,2,1] ![1,1,1] ![32,4,2] := by decide +kernel
#print axioms leaf01328_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
