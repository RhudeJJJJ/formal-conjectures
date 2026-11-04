/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01666Outer05

/-!
# Original leaf 01666 — Outer06

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01666.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01666_w_source06 : NestedInteger.Poly 3 := leaf01666_w_source05.drop 12
def leaf01666_w_segment06 : NestedInteger.Poly 3 := leaf01666_w_source06.take 12
def leaf01666_w_weights06 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 12 1 128 72 leaf01666_w_segment06)
theorem leaf01666_w_weights06_identity : leaf01666_w_weights06=IntegerWeightedOuter.weights 12 1 128 72 leaf01666_w_segment06 := by decide +kernel
def leaf01666_w_piece06 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01666_w_weights06 leaf01666_w_segment06)
theorem leaf01666_w_piece06_weighted : leaf01666_w_piece06=IntegerWeightedOuter.applyWeights leaf01666_w_weights06 leaf01666_w_segment06 := by decide +kernel
theorem leaf01666_w_piece06_identity : leaf01666_w_piece06=IntegerOuterTerms.transform 12 1 128 72 leaf01666_w_segment06 :=
  IntegerWeightedOuter.checked 12 1 128 72 leaf01666_w_segment06 leaf01666_w_piece06 leaf01666_w_weights06 leaf01666_w_weights06_identity leaf01666_w_piece06_weighted
#print axioms leaf01666_w_weights06_identity
#print axioms leaf01666_w_piece06_weighted
#print axioms leaf01666_w_piece06_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
