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
noncomputable def leaf01341_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 1000960513101371801600000000000 1170331283337722090311448629271 62771389600662576197000000000000))
theorem leaf01341_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 1000960513101371801600000000000 1170331283337722090311448629271 62771389600662576197000000000000 leaf01341_w_raw=true := by decide +kernel
theorem leaf01341_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01341_w_raw=true := by decide +kernel
#print axioms leaf01341_raw
#print axioms leaf01341_rectangular
noncomputable def leaf01341_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01341_w_raw ![12,255,254] ![1,1,1] ![32,256,256])
theorem leaf01341_inner : leaf01341_w_inner=IntegerAffineStages.inner leaf01341_w_raw ![12,255,254] ![1,1,1] ![32,256,256] := by decide +kernel
#print axioms leaf01341_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
