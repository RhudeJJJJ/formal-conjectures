/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD3Long00StagedIntegerNorm
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00004_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial FixedDegree03Long00StagedIntegerNorm.pack false 1154329073939143627078833170022400000000000 696746728664192206214242628863056827 114015785369235776341753308200000000000))
theorem leaf00004_raw : IntegerNormProgramPack.rawCheck FixedDegree03Long00StagedIntegerNorm.pack false 1154329073939143627078833170022400000000000 696746728664192206214242628863056827 114015785369235776341753308200000000000 leaf00004_w_raw=true := by decide +kernel
theorem leaf00004_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf00004_w_raw=true := by decide +kernel
#print axioms leaf00004_raw
#print axioms leaf00004_rectangular
noncomputable def leaf00004_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf00004_w_raw ![33,0,0] ![1,1,1] ![32000,1,1])
theorem leaf00004_inner : leaf00004_w_inner=IntegerAffineStages.inner leaf00004_w_raw ![33,0,0] ![1,1,1] ![32000,1,1] := by decide +kernel
#print axioms leaf00004_inner
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0001
