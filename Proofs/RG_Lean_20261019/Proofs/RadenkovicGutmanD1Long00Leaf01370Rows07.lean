/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01370Affine

/-!
# Bernstein row certificates 7 for leaf 01370

These declarations retain the original polynomial data and proof bodies.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01370.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01370_w_row070 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row070 leaf01370_w_affine)
theorem leaf01370_w_row070_weighted : leaf01370_w_row070=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row070 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row070_identity : leaf01370_w_row070=NestedInteger.coefficientFrom 88 70 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 70 0 leaf01370_w_affine leaf01370_w_row070 IntegerBernsteinWeights88.row070 (IntegerBernsteinTable.checked (n := 2) 88 70 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row070 leaf01370_w_affine_length IntegerBernsteinWeights88.row070_identity) leaf01370_w_row070_weighted
theorem leaf01370_w_row070_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row070=true := by decide +kernel
#print axioms leaf01370_w_row070_weighted
#print axioms leaf01370_w_row070_identity
#print axioms leaf01370_w_row070_positive
def leaf01370_w_row071 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row071 leaf01370_w_affine)
theorem leaf01370_w_row071_weighted : leaf01370_w_row071=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row071 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row071_identity : leaf01370_w_row071=NestedInteger.coefficientFrom 88 71 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 71 0 leaf01370_w_affine leaf01370_w_row071 IntegerBernsteinWeights88.row071 (IntegerBernsteinTable.checked (n := 2) 88 71 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row071 leaf01370_w_affine_length IntegerBernsteinWeights88.row071_identity) leaf01370_w_row071_weighted
theorem leaf01370_w_row071_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row071=true := by decide +kernel
#print axioms leaf01370_w_row071_weighted
#print axioms leaf01370_w_row071_identity
#print axioms leaf01370_w_row071_positive
def leaf01370_w_row072 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row072 leaf01370_w_affine)
theorem leaf01370_w_row072_weighted : leaf01370_w_row072=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row072 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row072_identity : leaf01370_w_row072=NestedInteger.coefficientFrom 88 72 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 72 0 leaf01370_w_affine leaf01370_w_row072 IntegerBernsteinWeights88.row072 (IntegerBernsteinTable.checked (n := 2) 88 72 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row072 leaf01370_w_affine_length IntegerBernsteinWeights88.row072_identity) leaf01370_w_row072_weighted
theorem leaf01370_w_row072_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row072=true := by decide +kernel
#print axioms leaf01370_w_row072_weighted
#print axioms leaf01370_w_row072_identity
#print axioms leaf01370_w_row072_positive
def leaf01370_w_row073 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row073 leaf01370_w_affine)
theorem leaf01370_w_row073_weighted : leaf01370_w_row073=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row073 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row073_identity : leaf01370_w_row073=NestedInteger.coefficientFrom 88 73 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 73 0 leaf01370_w_affine leaf01370_w_row073 IntegerBernsteinWeights88.row073 (IntegerBernsteinTable.checked (n := 2) 88 73 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row073 leaf01370_w_affine_length IntegerBernsteinWeights88.row073_identity) leaf01370_w_row073_weighted
theorem leaf01370_w_row073_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row073=true := by decide +kernel
#print axioms leaf01370_w_row073_weighted
#print axioms leaf01370_w_row073_identity
#print axioms leaf01370_w_row073_positive
def leaf01370_w_row074 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row074 leaf01370_w_affine)
theorem leaf01370_w_row074_weighted : leaf01370_w_row074=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row074 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row074_identity : leaf01370_w_row074=NestedInteger.coefficientFrom 88 74 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 74 0 leaf01370_w_affine leaf01370_w_row074 IntegerBernsteinWeights88.row074 (IntegerBernsteinTable.checked (n := 2) 88 74 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row074 leaf01370_w_affine_length IntegerBernsteinWeights88.row074_identity) leaf01370_w_row074_weighted
theorem leaf01370_w_row074_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row074=true := by decide +kernel
#print axioms leaf01370_w_row074_weighted
#print axioms leaf01370_w_row074_identity
#print axioms leaf01370_w_row074_positive
def leaf01370_w_row075 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row075 leaf01370_w_affine)
theorem leaf01370_w_row075_weighted : leaf01370_w_row075=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row075 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row075_identity : leaf01370_w_row075=NestedInteger.coefficientFrom 88 75 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 75 0 leaf01370_w_affine leaf01370_w_row075 IntegerBernsteinWeights88.row075 (IntegerBernsteinTable.checked (n := 2) 88 75 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row075 leaf01370_w_affine_length IntegerBernsteinWeights88.row075_identity) leaf01370_w_row075_weighted
theorem leaf01370_w_row075_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row075=true := by decide +kernel
#print axioms leaf01370_w_row075_weighted
#print axioms leaf01370_w_row075_identity
#print axioms leaf01370_w_row075_positive
def leaf01370_w_row076 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row076 leaf01370_w_affine)
theorem leaf01370_w_row076_weighted : leaf01370_w_row076=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row076 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row076_identity : leaf01370_w_row076=NestedInteger.coefficientFrom 88 76 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 76 0 leaf01370_w_affine leaf01370_w_row076 IntegerBernsteinWeights88.row076 (IntegerBernsteinTable.checked (n := 2) 88 76 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row076 leaf01370_w_affine_length IntegerBernsteinWeights88.row076_identity) leaf01370_w_row076_weighted
theorem leaf01370_w_row076_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row076=true := by decide +kernel
#print axioms leaf01370_w_row076_weighted
#print axioms leaf01370_w_row076_identity
#print axioms leaf01370_w_row076_positive
def leaf01370_w_row077 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row077 leaf01370_w_affine)
theorem leaf01370_w_row077_weighted : leaf01370_w_row077=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row077 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row077_identity : leaf01370_w_row077=NestedInteger.coefficientFrom 88 77 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 77 0 leaf01370_w_affine leaf01370_w_row077 IntegerBernsteinWeights88.row077 (IntegerBernsteinTable.checked (n := 2) 88 77 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row077 leaf01370_w_affine_length IntegerBernsteinWeights88.row077_identity) leaf01370_w_row077_weighted
theorem leaf01370_w_row077_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row077=true := by decide +kernel
#print axioms leaf01370_w_row077_weighted
#print axioms leaf01370_w_row077_identity
#print axioms leaf01370_w_row077_positive
def leaf01370_w_row078 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row078 leaf01370_w_affine)
theorem leaf01370_w_row078_weighted : leaf01370_w_row078=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row078 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row078_identity : leaf01370_w_row078=NestedInteger.coefficientFrom 88 78 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 78 0 leaf01370_w_affine leaf01370_w_row078 IntegerBernsteinWeights88.row078 (IntegerBernsteinTable.checked (n := 2) 88 78 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row078 leaf01370_w_affine_length IntegerBernsteinWeights88.row078_identity) leaf01370_w_row078_weighted
theorem leaf01370_w_row078_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row078=true := by decide +kernel
#print axioms leaf01370_w_row078_weighted
#print axioms leaf01370_w_row078_identity
#print axioms leaf01370_w_row078_positive
def leaf01370_w_row079 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row079 leaf01370_w_affine)
theorem leaf01370_w_row079_weighted : leaf01370_w_row079=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row079 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row079_identity : leaf01370_w_row079=NestedInteger.coefficientFrom 88 79 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 79 0 leaf01370_w_affine leaf01370_w_row079 IntegerBernsteinWeights88.row079 (IntegerBernsteinTable.checked (n := 2) 88 79 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row079 leaf01370_w_affine_length IntegerBernsteinWeights88.row079_identity) leaf01370_w_row079_weighted
theorem leaf01370_w_row079_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row079=true := by decide +kernel
#print axioms leaf01370_w_row079_weighted
#print axioms leaf01370_w_row079_identity
#print axioms leaf01370_w_row079_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
