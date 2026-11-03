/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01370Affine

/-!
# Bernstein row certificates 6 for leaf 01370

These declarations retain the original polynomial data and proof bodies.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01370.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01370_w_row060 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row060 leaf01370_w_affine)
theorem leaf01370_w_row060_weighted : leaf01370_w_row060=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row060 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row060_identity : leaf01370_w_row060=NestedInteger.coefficientFrom 88 60 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 60 0 leaf01370_w_affine leaf01370_w_row060 IntegerBernsteinWeights88.row060 (IntegerBernsteinTable.checked (n := 2) 88 60 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row060 leaf01370_w_affine_length IntegerBernsteinWeights88.row060_identity) leaf01370_w_row060_weighted
theorem leaf01370_w_row060_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row060=true := by decide +kernel
#print axioms leaf01370_w_row060_weighted
#print axioms leaf01370_w_row060_identity
#print axioms leaf01370_w_row060_positive
def leaf01370_w_row061 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row061 leaf01370_w_affine)
theorem leaf01370_w_row061_weighted : leaf01370_w_row061=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row061 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row061_identity : leaf01370_w_row061=NestedInteger.coefficientFrom 88 61 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 61 0 leaf01370_w_affine leaf01370_w_row061 IntegerBernsteinWeights88.row061 (IntegerBernsteinTable.checked (n := 2) 88 61 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row061 leaf01370_w_affine_length IntegerBernsteinWeights88.row061_identity) leaf01370_w_row061_weighted
theorem leaf01370_w_row061_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row061=true := by decide +kernel
#print axioms leaf01370_w_row061_weighted
#print axioms leaf01370_w_row061_identity
#print axioms leaf01370_w_row061_positive
def leaf01370_w_row062 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row062 leaf01370_w_affine)
theorem leaf01370_w_row062_weighted : leaf01370_w_row062=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row062 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row062_identity : leaf01370_w_row062=NestedInteger.coefficientFrom 88 62 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 62 0 leaf01370_w_affine leaf01370_w_row062 IntegerBernsteinWeights88.row062 (IntegerBernsteinTable.checked (n := 2) 88 62 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row062 leaf01370_w_affine_length IntegerBernsteinWeights88.row062_identity) leaf01370_w_row062_weighted
theorem leaf01370_w_row062_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row062=true := by decide +kernel
#print axioms leaf01370_w_row062_weighted
#print axioms leaf01370_w_row062_identity
#print axioms leaf01370_w_row062_positive
def leaf01370_w_row063 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row063 leaf01370_w_affine)
theorem leaf01370_w_row063_weighted : leaf01370_w_row063=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row063 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row063_identity : leaf01370_w_row063=NestedInteger.coefficientFrom 88 63 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 63 0 leaf01370_w_affine leaf01370_w_row063 IntegerBernsteinWeights88.row063 (IntegerBernsteinTable.checked (n := 2) 88 63 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row063 leaf01370_w_affine_length IntegerBernsteinWeights88.row063_identity) leaf01370_w_row063_weighted
theorem leaf01370_w_row063_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row063=true := by decide +kernel
#print axioms leaf01370_w_row063_weighted
#print axioms leaf01370_w_row063_identity
#print axioms leaf01370_w_row063_positive
def leaf01370_w_row064 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row064 leaf01370_w_affine)
theorem leaf01370_w_row064_weighted : leaf01370_w_row064=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row064 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row064_identity : leaf01370_w_row064=NestedInteger.coefficientFrom 88 64 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 64 0 leaf01370_w_affine leaf01370_w_row064 IntegerBernsteinWeights88.row064 (IntegerBernsteinTable.checked (n := 2) 88 64 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row064 leaf01370_w_affine_length IntegerBernsteinWeights88.row064_identity) leaf01370_w_row064_weighted
theorem leaf01370_w_row064_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row064=true := by decide +kernel
#print axioms leaf01370_w_row064_weighted
#print axioms leaf01370_w_row064_identity
#print axioms leaf01370_w_row064_positive
def leaf01370_w_row065 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row065 leaf01370_w_affine)
theorem leaf01370_w_row065_weighted : leaf01370_w_row065=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row065 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row065_identity : leaf01370_w_row065=NestedInteger.coefficientFrom 88 65 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 65 0 leaf01370_w_affine leaf01370_w_row065 IntegerBernsteinWeights88.row065 (IntegerBernsteinTable.checked (n := 2) 88 65 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row065 leaf01370_w_affine_length IntegerBernsteinWeights88.row065_identity) leaf01370_w_row065_weighted
theorem leaf01370_w_row065_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row065=true := by decide +kernel
#print axioms leaf01370_w_row065_weighted
#print axioms leaf01370_w_row065_identity
#print axioms leaf01370_w_row065_positive
def leaf01370_w_row066 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row066 leaf01370_w_affine)
theorem leaf01370_w_row066_weighted : leaf01370_w_row066=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row066 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row066_identity : leaf01370_w_row066=NestedInteger.coefficientFrom 88 66 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 66 0 leaf01370_w_affine leaf01370_w_row066 IntegerBernsteinWeights88.row066 (IntegerBernsteinTable.checked (n := 2) 88 66 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row066 leaf01370_w_affine_length IntegerBernsteinWeights88.row066_identity) leaf01370_w_row066_weighted
theorem leaf01370_w_row066_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row066=true := by decide +kernel
#print axioms leaf01370_w_row066_weighted
#print axioms leaf01370_w_row066_identity
#print axioms leaf01370_w_row066_positive
def leaf01370_w_row067 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row067 leaf01370_w_affine)
theorem leaf01370_w_row067_weighted : leaf01370_w_row067=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row067 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row067_identity : leaf01370_w_row067=NestedInteger.coefficientFrom 88 67 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 67 0 leaf01370_w_affine leaf01370_w_row067 IntegerBernsteinWeights88.row067 (IntegerBernsteinTable.checked (n := 2) 88 67 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row067 leaf01370_w_affine_length IntegerBernsteinWeights88.row067_identity) leaf01370_w_row067_weighted
theorem leaf01370_w_row067_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row067=true := by decide +kernel
#print axioms leaf01370_w_row067_weighted
#print axioms leaf01370_w_row067_identity
#print axioms leaf01370_w_row067_positive
def leaf01370_w_row068 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row068 leaf01370_w_affine)
theorem leaf01370_w_row068_weighted : leaf01370_w_row068=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row068 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row068_identity : leaf01370_w_row068=NestedInteger.coefficientFrom 88 68 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 68 0 leaf01370_w_affine leaf01370_w_row068 IntegerBernsteinWeights88.row068 (IntegerBernsteinTable.checked (n := 2) 88 68 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row068 leaf01370_w_affine_length IntegerBernsteinWeights88.row068_identity) leaf01370_w_row068_weighted
theorem leaf01370_w_row068_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row068=true := by decide +kernel
#print axioms leaf01370_w_row068_weighted
#print axioms leaf01370_w_row068_identity
#print axioms leaf01370_w_row068_positive
def leaf01370_w_row069 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row069 leaf01370_w_affine)
theorem leaf01370_w_row069_weighted : leaf01370_w_row069=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row069 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row069_identity : leaf01370_w_row069=NestedInteger.coefficientFrom 88 69 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 69 0 leaf01370_w_affine leaf01370_w_row069 IntegerBernsteinWeights88.row069 (IntegerBernsteinTable.checked (n := 2) 88 69 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row069 leaf01370_w_affine_length IntegerBernsteinWeights88.row069_identity) leaf01370_w_row069_weighted
theorem leaf01370_w_row069_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row069=true := by decide +kernel
#print axioms leaf01370_w_row069_weighted
#print axioms leaf01370_w_row069_identity
#print axioms leaf01370_w_row069_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
