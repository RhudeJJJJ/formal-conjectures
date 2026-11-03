/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88

/-!
# Exact polynomial and inner transformation for leaf 01370

These declarations retain the original polynomial data and proof bodies.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01370.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01370_w_raw : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 52044008913895424000000000000 59017741855377244050538071987 4756327498608298196531250000000))
theorem leaf01370_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 52044008913895424000000000000 59017741855377244050538071987 4756327498608298196531250000000 leaf01370_w_raw=true := by decide +kernel
theorem leaf01370_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01370_w_raw=true := by decide +kernel
#print axioms leaf01370_raw
#print axioms leaf01370_rectangular
def leaf01370_w_inner : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerAffineStages.inner leaf01370_w_raw ![10,62,31] ![1,1,1] ![32,64,32])
theorem leaf01370_inner : leaf01370_w_inner=IntegerAffineStages.inner leaf01370_w_raw ![10,62,31] ![1,1,1] ![32,64,32] := by decide +kernel
#print axioms leaf01370_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
