/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD2Long00CompositionalIntegerNorm
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf06289_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial FixedDegree02Long00CompositionalIntegerNorm.pack true 521821496357095796113408000000000000 521823486595410820160128536031915761 393532041173009668295722877852123500000000000))
theorem leaf06289_raw : IntegerNormProgramPack.rawCheck FixedDegree02Long00CompositionalIntegerNorm.pack true 521821496357095796113408000000000000 521823486595410820160128536031915761 393532041173009668295722877852123500000000000 leaf06289_w_raw=true := by decide +kernel
theorem leaf06289_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf06289_w_raw=true := by decide +kernel
#print axioms leaf06289_raw
#print axioms leaf06289_rectangular
noncomputable def leaf06289_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf06289_w_raw ![4,0,0] ![1,1,1] ![4096,1,1])
theorem leaf06289_inner : leaf06289_w_inner=IntegerAffineStages.inner leaf06289_w_raw ![4,0,0] ![1,1,1] ![4096,1,1] := by decide +kernel
#print axioms leaf06289_inner
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00SegmentedIntegerLeaf06289
