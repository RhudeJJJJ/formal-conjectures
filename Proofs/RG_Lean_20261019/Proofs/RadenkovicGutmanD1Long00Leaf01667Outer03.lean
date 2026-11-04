/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01667Outer02

/-!
# Original leaf 01667 — Outer03

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01667.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01667_w_source03 : NestedInteger.Poly 3 := leaf01667_w_source02.drop 12
def leaf01667_w_segment03 : NestedInteger.Poly 3 := leaf01667_w_source03.take 12
def leaf01667_w_weights03 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 12 1 128 36 leaf01667_w_segment03)
theorem leaf01667_w_weights03_identity : leaf01667_w_weights03=IntegerWeightedOuter.weights 12 1 128 36 leaf01667_w_segment03 := by decide +kernel
def leaf01667_w_piece03 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01667_w_weights03 leaf01667_w_segment03)
theorem leaf01667_w_piece03_weighted : leaf01667_w_piece03=IntegerWeightedOuter.applyWeights leaf01667_w_weights03 leaf01667_w_segment03 := by decide +kernel
theorem leaf01667_w_piece03_identity : leaf01667_w_piece03=IntegerOuterTerms.transform 12 1 128 36 leaf01667_w_segment03 :=
  IntegerWeightedOuter.checked 12 1 128 36 leaf01667_w_segment03 leaf01667_w_piece03 leaf01667_w_weights03 leaf01667_w_weights03_identity leaf01667_w_piece03_weighted
#print axioms leaf01667_w_weights03_identity
#print axioms leaf01667_w_piece03_weighted
#print axioms leaf01667_w_piece03_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
