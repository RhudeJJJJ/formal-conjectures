/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01668Outer00

/-!
# Original leaf 01668 — Outer01

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01668.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01668_w_source01 : NestedInteger.Poly 3 := leaf01668_w_source00.drop 12
def leaf01668_w_segment01 : NestedInteger.Poly 3 := leaf01668_w_source01.take 12
def leaf01668_w_weights01 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 12 1 128 12 leaf01668_w_segment01)
theorem leaf01668_w_weights01_identity : leaf01668_w_weights01=IntegerWeightedOuter.weights 12 1 128 12 leaf01668_w_segment01 := by decide +kernel
def leaf01668_w_piece01 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01668_w_weights01 leaf01668_w_segment01)
theorem leaf01668_w_piece01_weighted : leaf01668_w_piece01=IntegerWeightedOuter.applyWeights leaf01668_w_weights01 leaf01668_w_segment01 := by decide +kernel
theorem leaf01668_w_piece01_identity : leaf01668_w_piece01=IntegerOuterTerms.transform 12 1 128 12 leaf01668_w_segment01 :=
  IntegerWeightedOuter.checked 12 1 128 12 leaf01668_w_segment01 leaf01668_w_piece01 leaf01668_w_weights01 leaf01668_w_weights01_identity leaf01668_w_piece01_weighted
#print axioms leaf01668_w_weights01_identity
#print axioms leaf01668_w_piece01_weighted
#print axioms leaf01668_w_piece01_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
