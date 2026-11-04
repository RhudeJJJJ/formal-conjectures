/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01666Affine

/-!
# Original leaf 01666 — Rows03

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01666.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01666_w_row030 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf01666_w_affine)
theorem leaf01666_w_row030_weighted : leaf01666_w_row030=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row030 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row030_identity : leaf01666_w_row030=NestedInteger.coefficientFrom 88 30 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 30 0 leaf01666_w_affine leaf01666_w_row030 IntegerBernsteinWeights88.row030 (IntegerBernsteinTable.checked (n := 2) 88 30 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row030 leaf01666_w_affine_length IntegerBernsteinWeights88.row030_identity) leaf01666_w_row030_weighted
theorem leaf01666_w_row030_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row030=true := by decide +kernel
#print axioms leaf01666_w_row030_weighted
#print axioms leaf01666_w_row030_identity
#print axioms leaf01666_w_row030_positive
def leaf01666_w_row031 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row031 leaf01666_w_affine)
theorem leaf01666_w_row031_weighted : leaf01666_w_row031=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row031 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row031_identity : leaf01666_w_row031=NestedInteger.coefficientFrom 88 31 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 31 0 leaf01666_w_affine leaf01666_w_row031 IntegerBernsteinWeights88.row031 (IntegerBernsteinTable.checked (n := 2) 88 31 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row031 leaf01666_w_affine_length IntegerBernsteinWeights88.row031_identity) leaf01666_w_row031_weighted
theorem leaf01666_w_row031_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row031=true := by decide +kernel
#print axioms leaf01666_w_row031_weighted
#print axioms leaf01666_w_row031_identity
#print axioms leaf01666_w_row031_positive
def leaf01666_w_row032 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01666_w_affine)
theorem leaf01666_w_row032_weighted : leaf01666_w_row032=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row032_identity : leaf01666_w_row032=NestedInteger.coefficientFrom 88 32 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 32 0 leaf01666_w_affine leaf01666_w_row032 IntegerBernsteinWeights88.row032 (IntegerBernsteinTable.checked (n := 2) 88 32 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row032 leaf01666_w_affine_length IntegerBernsteinWeights88.row032_identity) leaf01666_w_row032_weighted
theorem leaf01666_w_row032_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row032=true := by decide +kernel
#print axioms leaf01666_w_row032_weighted
#print axioms leaf01666_w_row032_identity
#print axioms leaf01666_w_row032_positive
def leaf01666_w_row033 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row033 leaf01666_w_affine)
theorem leaf01666_w_row033_weighted : leaf01666_w_row033=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row033 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row033_identity : leaf01666_w_row033=NestedInteger.coefficientFrom 88 33 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 33 0 leaf01666_w_affine leaf01666_w_row033 IntegerBernsteinWeights88.row033 (IntegerBernsteinTable.checked (n := 2) 88 33 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row033 leaf01666_w_affine_length IntegerBernsteinWeights88.row033_identity) leaf01666_w_row033_weighted
theorem leaf01666_w_row033_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row033=true := by decide +kernel
#print axioms leaf01666_w_row033_weighted
#print axioms leaf01666_w_row033_identity
#print axioms leaf01666_w_row033_positive
def leaf01666_w_row034 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf01666_w_affine)
theorem leaf01666_w_row034_weighted : leaf01666_w_row034=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row034 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row034_identity : leaf01666_w_row034=NestedInteger.coefficientFrom 88 34 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 34 0 leaf01666_w_affine leaf01666_w_row034 IntegerBernsteinWeights88.row034 (IntegerBernsteinTable.checked (n := 2) 88 34 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row034 leaf01666_w_affine_length IntegerBernsteinWeights88.row034_identity) leaf01666_w_row034_weighted
theorem leaf01666_w_row034_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row034=true := by decide +kernel
#print axioms leaf01666_w_row034_weighted
#print axioms leaf01666_w_row034_identity
#print axioms leaf01666_w_row034_positive
def leaf01666_w_row035 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row035 leaf01666_w_affine)
theorem leaf01666_w_row035_weighted : leaf01666_w_row035=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row035 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row035_identity : leaf01666_w_row035=NestedInteger.coefficientFrom 88 35 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 35 0 leaf01666_w_affine leaf01666_w_row035 IntegerBernsteinWeights88.row035 (IntegerBernsteinTable.checked (n := 2) 88 35 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row035 leaf01666_w_affine_length IntegerBernsteinWeights88.row035_identity) leaf01666_w_row035_weighted
theorem leaf01666_w_row035_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row035=true := by decide +kernel
#print axioms leaf01666_w_row035_weighted
#print axioms leaf01666_w_row035_identity
#print axioms leaf01666_w_row035_positive
def leaf01666_w_row036 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row036 leaf01666_w_affine)
theorem leaf01666_w_row036_weighted : leaf01666_w_row036=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row036 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row036_identity : leaf01666_w_row036=NestedInteger.coefficientFrom 88 36 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 36 0 leaf01666_w_affine leaf01666_w_row036 IntegerBernsteinWeights88.row036 (IntegerBernsteinTable.checked (n := 2) 88 36 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row036 leaf01666_w_affine_length IntegerBernsteinWeights88.row036_identity) leaf01666_w_row036_weighted
theorem leaf01666_w_row036_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row036=true := by decide +kernel
#print axioms leaf01666_w_row036_weighted
#print axioms leaf01666_w_row036_identity
#print axioms leaf01666_w_row036_positive
def leaf01666_w_row037 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row037 leaf01666_w_affine)
theorem leaf01666_w_row037_weighted : leaf01666_w_row037=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row037 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row037_identity : leaf01666_w_row037=NestedInteger.coefficientFrom 88 37 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 37 0 leaf01666_w_affine leaf01666_w_row037 IntegerBernsteinWeights88.row037 (IntegerBernsteinTable.checked (n := 2) 88 37 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row037 leaf01666_w_affine_length IntegerBernsteinWeights88.row037_identity) leaf01666_w_row037_weighted
theorem leaf01666_w_row037_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row037=true := by decide +kernel
#print axioms leaf01666_w_row037_weighted
#print axioms leaf01666_w_row037_identity
#print axioms leaf01666_w_row037_positive
def leaf01666_w_row038 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row038 leaf01666_w_affine)
theorem leaf01666_w_row038_weighted : leaf01666_w_row038=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row038 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row038_identity : leaf01666_w_row038=NestedInteger.coefficientFrom 88 38 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 38 0 leaf01666_w_affine leaf01666_w_row038 IntegerBernsteinWeights88.row038 (IntegerBernsteinTable.checked (n := 2) 88 38 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row038 leaf01666_w_affine_length IntegerBernsteinWeights88.row038_identity) leaf01666_w_row038_weighted
theorem leaf01666_w_row038_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row038=true := by decide +kernel
#print axioms leaf01666_w_row038_weighted
#print axioms leaf01666_w_row038_identity
#print axioms leaf01666_w_row038_positive
def leaf01666_w_row039 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row039 leaf01666_w_affine)
theorem leaf01666_w_row039_weighted : leaf01666_w_row039=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row039 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row039_identity : leaf01666_w_row039=NestedInteger.coefficientFrom 88 39 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 39 0 leaf01666_w_affine leaf01666_w_row039 IntegerBernsteinWeights88.row039 (IntegerBernsteinTable.checked (n := 2) 88 39 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row039 leaf01666_w_affine_length IntegerBernsteinWeights88.row039_identity) leaf01666_w_row039_weighted
theorem leaf01666_w_row039_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row039=true := by decide +kernel
#print axioms leaf01666_w_row039_weighted
#print axioms leaf01666_w_row039_identity
#print axioms leaf01666_w_row039_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
