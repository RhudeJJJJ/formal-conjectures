/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD4Long00CompositionalIntegerNorm
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00935_w_raw : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial FixedDegree04Long00CompositionalIntegerNorm.pack true 17175246898196899642212352000000000000 17175377916423728793966141883797519527 4722402506577874290339879539124971000000000000))
theorem leaf00935_raw : IntegerNormProgramPack.rawCheck FixedDegree04Long00CompositionalIntegerNorm.pack true 17175246898196899642212352000000000000 17175377916423728793966141883797519527 4722402506577874290339879539124971000000000000 leaf00935_w_raw=true := by decide +kernel
theorem leaf00935_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf00935_w_raw=true := by decide +kernel
#print axioms leaf00935_raw
#print axioms leaf00935_rectangular
noncomputable def leaf00935_w_inner : NestedInteger.Poly 3 := rg_closed_integer_data%
  (IntegerAffineStages.inner leaf00935_w_raw ![2,1,1] ![1,1,1] ![2048,2,2])
theorem leaf00935_inner : leaf00935_w_inner=IntegerAffineStages.inner leaf00935_w_raw ![2,1,1] ![1,1,1] ![2048,2,2] := by decide +kernel
#print axioms leaf00935_inner
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00SegmentedIntegerLeaf00935
