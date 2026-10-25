/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD3Long00StagedIntegerNorm
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial FixedDegree03Long00StagedIntegerNorm.pack false 559938542576676700115808813056000000000 308373619350145096512854599795773 52014752816231130849240360000000000))
theorem leaf00000_raw : IntegerNormProgramPack.rawCheck FixedDegree03Long00StagedIntegerNorm.pack false 559938542576676700115808813056000000000 308373619350145096512854599795773 52014752816231130849240360000000000 leaf00000_w_raw=true := by decide +kernel
theorem leaf00000_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf00000_w_raw=true := by decide +kernel
#print axioms leaf00000_raw
#print axioms leaf00000_rectangular
noncomputable def leaf00000_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf00000_w_raw ![32,0,0] ![1,1,1] ![32000,2,2])
theorem leaf00000_inner : leaf00000_w_inner=IntegerAffineStages.inner leaf00000_w_raw ![32,0,0] ![1,1,1] ![32000,2,2] := by decide +kernel
#print axioms leaf00000_inner
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00SegmentedIntegerLeaf00000
