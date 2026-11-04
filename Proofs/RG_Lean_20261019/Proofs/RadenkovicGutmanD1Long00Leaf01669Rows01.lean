/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01669Affine

/-!
# Original leaf 01669 — Rows01

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01669.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01669_w_row010 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row010 leaf01669_w_affine)
theorem leaf01669_w_row010_weighted : leaf01669_w_row010=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row010 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row010_identity : leaf01669_w_row010=NestedInteger.coefficientFrom 88 10 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 10 0 leaf01669_w_affine leaf01669_w_row010 IntegerBernsteinWeights88.row010 (IntegerBernsteinTable.checked (n := 2) 88 10 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row010 leaf01669_w_affine_length IntegerBernsteinWeights88.row010_identity) leaf01669_w_row010_weighted
theorem leaf01669_w_row010_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row010=true := by decide +kernel
#print axioms leaf01669_w_row010_weighted
#print axioms leaf01669_w_row010_identity
#print axioms leaf01669_w_row010_positive
def leaf01669_w_row011 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row011 leaf01669_w_affine)
theorem leaf01669_w_row011_weighted : leaf01669_w_row011=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row011 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row011_identity : leaf01669_w_row011=NestedInteger.coefficientFrom 88 11 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 11 0 leaf01669_w_affine leaf01669_w_row011 IntegerBernsteinWeights88.row011 (IntegerBernsteinTable.checked (n := 2) 88 11 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row011 leaf01669_w_affine_length IntegerBernsteinWeights88.row011_identity) leaf01669_w_row011_weighted
theorem leaf01669_w_row011_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row011=true := by decide +kernel
#print axioms leaf01669_w_row011_weighted
#print axioms leaf01669_w_row011_identity
#print axioms leaf01669_w_row011_positive
def leaf01669_w_row012 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row012 leaf01669_w_affine)
theorem leaf01669_w_row012_weighted : leaf01669_w_row012=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row012 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row012_identity : leaf01669_w_row012=NestedInteger.coefficientFrom 88 12 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 12 0 leaf01669_w_affine leaf01669_w_row012 IntegerBernsteinWeights88.row012 (IntegerBernsteinTable.checked (n := 2) 88 12 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row012 leaf01669_w_affine_length IntegerBernsteinWeights88.row012_identity) leaf01669_w_row012_weighted
theorem leaf01669_w_row012_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row012=true := by decide +kernel
#print axioms leaf01669_w_row012_weighted
#print axioms leaf01669_w_row012_identity
#print axioms leaf01669_w_row012_positive
def leaf01669_w_row013 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row013 leaf01669_w_affine)
theorem leaf01669_w_row013_weighted : leaf01669_w_row013=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row013 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row013_identity : leaf01669_w_row013=NestedInteger.coefficientFrom 88 13 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 13 0 leaf01669_w_affine leaf01669_w_row013 IntegerBernsteinWeights88.row013 (IntegerBernsteinTable.checked (n := 2) 88 13 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row013 leaf01669_w_affine_length IntegerBernsteinWeights88.row013_identity) leaf01669_w_row013_weighted
theorem leaf01669_w_row013_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row013=true := by decide +kernel
#print axioms leaf01669_w_row013_weighted
#print axioms leaf01669_w_row013_identity
#print axioms leaf01669_w_row013_positive
def leaf01669_w_row014 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row014 leaf01669_w_affine)
theorem leaf01669_w_row014_weighted : leaf01669_w_row014=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row014 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row014_identity : leaf01669_w_row014=NestedInteger.coefficientFrom 88 14 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 14 0 leaf01669_w_affine leaf01669_w_row014 IntegerBernsteinWeights88.row014 (IntegerBernsteinTable.checked (n := 2) 88 14 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row014 leaf01669_w_affine_length IntegerBernsteinWeights88.row014_identity) leaf01669_w_row014_weighted
theorem leaf01669_w_row014_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row014=true := by decide +kernel
#print axioms leaf01669_w_row014_weighted
#print axioms leaf01669_w_row014_identity
#print axioms leaf01669_w_row014_positive
def leaf01669_w_row015 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row015 leaf01669_w_affine)
theorem leaf01669_w_row015_weighted : leaf01669_w_row015=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row015 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row015_identity : leaf01669_w_row015=NestedInteger.coefficientFrom 88 15 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 15 0 leaf01669_w_affine leaf01669_w_row015 IntegerBernsteinWeights88.row015 (IntegerBernsteinTable.checked (n := 2) 88 15 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row015 leaf01669_w_affine_length IntegerBernsteinWeights88.row015_identity) leaf01669_w_row015_weighted
theorem leaf01669_w_row015_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row015=true := by decide +kernel
#print axioms leaf01669_w_row015_weighted
#print axioms leaf01669_w_row015_identity
#print axioms leaf01669_w_row015_positive
def leaf01669_w_row016 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row016 leaf01669_w_affine)
theorem leaf01669_w_row016_weighted : leaf01669_w_row016=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row016 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row016_identity : leaf01669_w_row016=NestedInteger.coefficientFrom 88 16 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 16 0 leaf01669_w_affine leaf01669_w_row016 IntegerBernsteinWeights88.row016 (IntegerBernsteinTable.checked (n := 2) 88 16 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row016 leaf01669_w_affine_length IntegerBernsteinWeights88.row016_identity) leaf01669_w_row016_weighted
theorem leaf01669_w_row016_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row016=true := by decide +kernel
#print axioms leaf01669_w_row016_weighted
#print axioms leaf01669_w_row016_identity
#print axioms leaf01669_w_row016_positive
def leaf01669_w_row017 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf01669_w_affine)
theorem leaf01669_w_row017_weighted : leaf01669_w_row017=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row017_identity : leaf01669_w_row017=NestedInteger.coefficientFrom 88 17 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 17 0 leaf01669_w_affine leaf01669_w_row017 IntegerBernsteinWeights88.row017 (IntegerBernsteinTable.checked (n := 2) 88 17 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row017 leaf01669_w_affine_length IntegerBernsteinWeights88.row017_identity) leaf01669_w_row017_weighted
theorem leaf01669_w_row017_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row017=true := by decide +kernel
#print axioms leaf01669_w_row017_weighted
#print axioms leaf01669_w_row017_identity
#print axioms leaf01669_w_row017_positive
def leaf01669_w_row018 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row018 leaf01669_w_affine)
theorem leaf01669_w_row018_weighted : leaf01669_w_row018=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row018 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row018_identity : leaf01669_w_row018=NestedInteger.coefficientFrom 88 18 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 18 0 leaf01669_w_affine leaf01669_w_row018 IntegerBernsteinWeights88.row018 (IntegerBernsteinTable.checked (n := 2) 88 18 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row018 leaf01669_w_affine_length IntegerBernsteinWeights88.row018_identity) leaf01669_w_row018_weighted
theorem leaf01669_w_row018_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row018=true := by decide +kernel
#print axioms leaf01669_w_row018_weighted
#print axioms leaf01669_w_row018_identity
#print axioms leaf01669_w_row018_positive
def leaf01669_w_row019 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row019 leaf01669_w_affine)
theorem leaf01669_w_row019_weighted : leaf01669_w_row019=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row019 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row019_identity : leaf01669_w_row019=NestedInteger.coefficientFrom 88 19 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 19 0 leaf01669_w_affine leaf01669_w_row019 IntegerBernsteinWeights88.row019 (IntegerBernsteinTable.checked (n := 2) 88 19 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row019 leaf01669_w_affine_length IntegerBernsteinWeights88.row019_identity) leaf01669_w_row019_weighted
theorem leaf01669_w_row019_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row019=true := by decide +kernel
#print axioms leaf01669_w_row019_weighted
#print axioms leaf01669_w_row019_identity
#print axioms leaf01669_w_row019_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
