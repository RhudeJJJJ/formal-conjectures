/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD3Long00StagedIntegerNorm
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial FixedDegree03Long00StagedIntegerNorm.pack true 469639346721386216502067200000000000 469642033531582541794697967988140249 236119674978171212566464538958341000000000000))
theorem leaf03800_raw : IntegerNormProgramPack.rawCheck FixedDegree03Long00StagedIntegerNorm.pack true 469639346721386216502067200000000000 469642033531582541794697967988140249 236119674978171212566464538958341000000000000 leaf03800_w_raw=true := by decide +kernel
theorem leaf03800_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf03800_w_raw=true := by decide +kernel
#print axioms leaf03800_raw
#print axioms leaf03800_rectangular
noncomputable def leaf03800_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf03800_w_raw ![4,0,0] ![1,1,1] ![4096,1,1])
theorem leaf03800_inner : leaf03800_w_inner=IntegerAffineStages.inner leaf03800_w_raw ![4,0,0] ![1,1,1] ![4096,1,1] := by decide +kernel
#print axioms leaf03800_inner
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
