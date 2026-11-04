/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01666Affine

/-!
# Original leaf 01666 — Rows05

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01666.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01666_w_row050 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row050 leaf01666_w_affine)
theorem leaf01666_w_row050_weighted : leaf01666_w_row050=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row050 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row050_identity : leaf01666_w_row050=NestedInteger.coefficientFrom 88 50 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 50 0 leaf01666_w_affine leaf01666_w_row050 IntegerBernsteinWeights88.row050 (IntegerBernsteinTable.checked (n := 2) 88 50 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row050 leaf01666_w_affine_length IntegerBernsteinWeights88.row050_identity) leaf01666_w_row050_weighted
theorem leaf01666_w_row050_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row050=true := by decide +kernel
#print axioms leaf01666_w_row050_weighted
#print axioms leaf01666_w_row050_identity
#print axioms leaf01666_w_row050_positive
def leaf01666_w_row051 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row051 leaf01666_w_affine)
theorem leaf01666_w_row051_weighted : leaf01666_w_row051=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row051 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row051_identity : leaf01666_w_row051=NestedInteger.coefficientFrom 88 51 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 51 0 leaf01666_w_affine leaf01666_w_row051 IntegerBernsteinWeights88.row051 (IntegerBernsteinTable.checked (n := 2) 88 51 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row051 leaf01666_w_affine_length IntegerBernsteinWeights88.row051_identity) leaf01666_w_row051_weighted
theorem leaf01666_w_row051_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row051=true := by decide +kernel
#print axioms leaf01666_w_row051_weighted
#print axioms leaf01666_w_row051_identity
#print axioms leaf01666_w_row051_positive
def leaf01666_w_row052 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row052 leaf01666_w_affine)
theorem leaf01666_w_row052_weighted : leaf01666_w_row052=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row052 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row052_identity : leaf01666_w_row052=NestedInteger.coefficientFrom 88 52 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 52 0 leaf01666_w_affine leaf01666_w_row052 IntegerBernsteinWeights88.row052 (IntegerBernsteinTable.checked (n := 2) 88 52 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row052 leaf01666_w_affine_length IntegerBernsteinWeights88.row052_identity) leaf01666_w_row052_weighted
theorem leaf01666_w_row052_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row052=true := by decide +kernel
#print axioms leaf01666_w_row052_weighted
#print axioms leaf01666_w_row052_identity
#print axioms leaf01666_w_row052_positive
def leaf01666_w_row053 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row053 leaf01666_w_affine)
theorem leaf01666_w_row053_weighted : leaf01666_w_row053=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row053 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row053_identity : leaf01666_w_row053=NestedInteger.coefficientFrom 88 53 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 53 0 leaf01666_w_affine leaf01666_w_row053 IntegerBernsteinWeights88.row053 (IntegerBernsteinTable.checked (n := 2) 88 53 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row053 leaf01666_w_affine_length IntegerBernsteinWeights88.row053_identity) leaf01666_w_row053_weighted
theorem leaf01666_w_row053_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row053=true := by decide +kernel
#print axioms leaf01666_w_row053_weighted
#print axioms leaf01666_w_row053_identity
#print axioms leaf01666_w_row053_positive
def leaf01666_w_row054 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row054 leaf01666_w_affine)
theorem leaf01666_w_row054_weighted : leaf01666_w_row054=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row054 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row054_identity : leaf01666_w_row054=NestedInteger.coefficientFrom 88 54 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 54 0 leaf01666_w_affine leaf01666_w_row054 IntegerBernsteinWeights88.row054 (IntegerBernsteinTable.checked (n := 2) 88 54 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row054 leaf01666_w_affine_length IntegerBernsteinWeights88.row054_identity) leaf01666_w_row054_weighted
theorem leaf01666_w_row054_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row054=true := by decide +kernel
#print axioms leaf01666_w_row054_weighted
#print axioms leaf01666_w_row054_identity
#print axioms leaf01666_w_row054_positive
def leaf01666_w_row055 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row055 leaf01666_w_affine)
theorem leaf01666_w_row055_weighted : leaf01666_w_row055=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row055 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row055_identity : leaf01666_w_row055=NestedInteger.coefficientFrom 88 55 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 55 0 leaf01666_w_affine leaf01666_w_row055 IntegerBernsteinWeights88.row055 (IntegerBernsteinTable.checked (n := 2) 88 55 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row055 leaf01666_w_affine_length IntegerBernsteinWeights88.row055_identity) leaf01666_w_row055_weighted
theorem leaf01666_w_row055_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row055=true := by decide +kernel
#print axioms leaf01666_w_row055_weighted
#print axioms leaf01666_w_row055_identity
#print axioms leaf01666_w_row055_positive
def leaf01666_w_row056 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row056 leaf01666_w_affine)
theorem leaf01666_w_row056_weighted : leaf01666_w_row056=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row056 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row056_identity : leaf01666_w_row056=NestedInteger.coefficientFrom 88 56 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 56 0 leaf01666_w_affine leaf01666_w_row056 IntegerBernsteinWeights88.row056 (IntegerBernsteinTable.checked (n := 2) 88 56 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row056 leaf01666_w_affine_length IntegerBernsteinWeights88.row056_identity) leaf01666_w_row056_weighted
theorem leaf01666_w_row056_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row056=true := by decide +kernel
#print axioms leaf01666_w_row056_weighted
#print axioms leaf01666_w_row056_identity
#print axioms leaf01666_w_row056_positive
def leaf01666_w_row057 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row057 leaf01666_w_affine)
theorem leaf01666_w_row057_weighted : leaf01666_w_row057=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row057 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row057_identity : leaf01666_w_row057=NestedInteger.coefficientFrom 88 57 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 57 0 leaf01666_w_affine leaf01666_w_row057 IntegerBernsteinWeights88.row057 (IntegerBernsteinTable.checked (n := 2) 88 57 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row057 leaf01666_w_affine_length IntegerBernsteinWeights88.row057_identity) leaf01666_w_row057_weighted
theorem leaf01666_w_row057_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row057=true := by decide +kernel
#print axioms leaf01666_w_row057_weighted
#print axioms leaf01666_w_row057_identity
#print axioms leaf01666_w_row057_positive
def leaf01666_w_row058 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row058 leaf01666_w_affine)
theorem leaf01666_w_row058_weighted : leaf01666_w_row058=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row058 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row058_identity : leaf01666_w_row058=NestedInteger.coefficientFrom 88 58 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 58 0 leaf01666_w_affine leaf01666_w_row058 IntegerBernsteinWeights88.row058 (IntegerBernsteinTable.checked (n := 2) 88 58 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row058 leaf01666_w_affine_length IntegerBernsteinWeights88.row058_identity) leaf01666_w_row058_weighted
theorem leaf01666_w_row058_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row058=true := by decide +kernel
#print axioms leaf01666_w_row058_weighted
#print axioms leaf01666_w_row058_identity
#print axioms leaf01666_w_row058_positive
def leaf01666_w_row059 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row059 leaf01666_w_affine)
theorem leaf01666_w_row059_weighted : leaf01666_w_row059=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row059 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row059_identity : leaf01666_w_row059=NestedInteger.coefficientFrom 88 59 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 59 0 leaf01666_w_affine leaf01666_w_row059 IntegerBernsteinWeights88.row059 (IntegerBernsteinTable.checked (n := 2) 88 59 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row059 leaf01666_w_affine_length IntegerBernsteinWeights88.row059_identity) leaf01666_w_row059_weighted
theorem leaf01666_w_row059_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row059=true := by decide +kernel
#print axioms leaf01666_w_row059_weighted
#print axioms leaf01666_w_row059_identity
#print axioms leaf01666_w_row059_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
