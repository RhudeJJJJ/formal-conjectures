/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD3Long00StagedIntegerNorm
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial FixedDegree03Long00StagedIntegerNorm.pack false 66308529413245738228751299248128000000000000 2126435531900274280437944565510893659776369 9465041651397827266621885266194250000000000))
theorem leaf01900_raw : IntegerNormProgramPack.rawCheck FixedDegree03Long00StagedIntegerNorm.pack false 66308529413245738228751299248128000000000000 2126435531900274280437944565510893659776369 9465041651397827266621885266194250000000000 leaf01900_w_raw=true := by decide +kernel
theorem leaf01900_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01900_w_raw=true := by decide +kernel
#print axioms leaf01900_raw
#print axioms leaf01900_rectangular
noncomputable def leaf01900_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf01900_w_raw ![559,0,0] ![3,1,1] ![12800,2,2])
theorem leaf01900_inner : leaf01900_w_inner=IntegerAffineStages.inner leaf01900_w_raw ![559,0,0] ![3,1,1] ![12800,2,2] := by decide +kernel
#print axioms leaf01900_inner
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf01900
