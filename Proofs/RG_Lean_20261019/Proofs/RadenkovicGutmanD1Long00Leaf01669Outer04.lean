/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01669Outer03

/-!
# Original leaf 01669 — Outer04

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01669.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01669_w_source04 : NestedInteger.Poly 3 := leaf01669_w_source03.drop 12
def leaf01669_w_segment04 : NestedInteger.Poly 3 := leaf01669_w_source04.take 12
def leaf01669_w_weights04 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 12 1 128 48 leaf01669_w_segment04)
theorem leaf01669_w_weights04_identity : leaf01669_w_weights04=IntegerWeightedOuter.weights 12 1 128 48 leaf01669_w_segment04 := by decide +kernel
def leaf01669_w_piece04 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01669_w_weights04 leaf01669_w_segment04)
theorem leaf01669_w_piece04_weighted : leaf01669_w_piece04=IntegerWeightedOuter.applyWeights leaf01669_w_weights04 leaf01669_w_segment04 := by decide +kernel
theorem leaf01669_w_piece04_identity : leaf01669_w_piece04=IntegerOuterTerms.transform 12 1 128 48 leaf01669_w_segment04 :=
  IntegerWeightedOuter.checked 12 1 128 48 leaf01669_w_segment04 leaf01669_w_piece04 leaf01669_w_weights04 leaf01669_w_weights04_identity leaf01669_w_piece04_weighted
#print axioms leaf01669_w_weights04_identity
#print axioms leaf01669_w_piece04_weighted
#print axioms leaf01669_w_piece04_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
