/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88

/-!
# Original leaf 01669 — Base

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01669.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01669_w_raw : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![88,4,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm00.pack true 4816675846016204800000000000 4897085356091602382550197181 10916668529567884087800000000000))
theorem leaf01669_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm00.pack true 4816675846016204800000000000 4897085356091602382550197181 10916668529567884087800000000000 leaf01669_w_raw=true := by decide +kernel
theorem leaf01669_rectangular : NestedInteger.rectangular 3 ![88,4,4] leaf01669_w_raw=true := by decide +kernel
#print axioms leaf01669_raw
#print axioms leaf01669_rectangular
def leaf01669_w_inner : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerAffineStages.inner leaf01669_w_raw ![12,3,2] ![1,1,1] ![128,4,4])
theorem leaf01669_inner : leaf01669_w_inner=IntegerAffineStages.inner leaf01669_w_raw ![12,3,2] ![1,1,1] ![128,4,4] := by decide +kernel
#print axioms leaf01669_inner
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
