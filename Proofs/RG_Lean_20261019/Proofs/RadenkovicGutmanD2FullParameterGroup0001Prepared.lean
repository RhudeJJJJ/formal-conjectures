/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD2Long00CompositionalIntegerNorm
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial FixedDegree02Long00CompositionalIntegerNorm.pack false 917210598499603621445072060416000000000000 1080856068203243453805414415813535407 86951787531791389637723024875000000000))
theorem leaf00005_raw : IntegerNormProgramPack.rawCheck FixedDegree02Long00CompositionalIntegerNorm.pack false 917210598499603621445072060416000000000000 1080856068203243453805414415813535407 86951787531791389637723024875000000000 leaf00005_w_raw=true := by decide +kernel
theorem leaf00005_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf00005_w_raw=true := by decide +kernel
#print axioms leaf00005_raw
#print axioms leaf00005_rectangular
noncomputable def leaf00005_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf00005_w_raw ![33,0,0] ![1,1,1] ![32000,1,1])
theorem leaf00005_inner : leaf00005_w_inner=IntegerAffineStages.inner leaf00005_w_raw ![33,0,0] ![1,1,1] ![32000,1,1] := by decide +kernel
#print axioms leaf00005_inner
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
