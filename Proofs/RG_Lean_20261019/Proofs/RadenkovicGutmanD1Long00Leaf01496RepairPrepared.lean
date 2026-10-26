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
noncomputable def leaf01496_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 69481858986095411200000000000 73639700285623707624312155817 22759905177356373534300000000000))
theorem leaf01496_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 69481858986095411200000000000 73639700285623707624312155817 22759905177356373534300000000000 leaf01496_w_raw=true := by decide +kernel
theorem leaf01496_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01496_w_raw=true := by decide +kernel
#print axioms leaf01496_raw
#print axioms leaf01496_rectangular
noncomputable def leaf01496_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01496_w_raw ![12,0,0] ![1,1,1] ![64,2,1])
theorem leaf01496_inner : leaf01496_w_inner=IntegerAffineStages.inner leaf01496_w_raw ![12,0,0] ![1,1,1] ![64,2,1] := by decide +kernel
#print axioms leaf01496_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
