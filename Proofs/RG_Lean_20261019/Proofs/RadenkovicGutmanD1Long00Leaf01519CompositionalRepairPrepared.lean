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
noncomputable def leaf01519_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 552133349298772377600000000000 580522887031826061207885023043 225790274898971688326500000000000))
theorem leaf01519_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 552133349298772377600000000000 580522887031826061207885023043 225790274898971688326500000000000 leaf01519_w_raw=true := by decide +kernel
theorem leaf01519_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01519_w_raw=true := by decide +kernel
#print axioms leaf01519_raw
#print axioms leaf01519_rectangular
noncomputable def leaf01519_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01519_w_raw ![11,14,7] ![1,1,1] ![64,16,8])
theorem leaf01519_inner : leaf01519_w_inner=IntegerAffineStages.inner leaf01519_w_raw ![11,14,7] ![1,1,1] ![64,16,8] := by decide +kernel
#print axioms leaf01519_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
