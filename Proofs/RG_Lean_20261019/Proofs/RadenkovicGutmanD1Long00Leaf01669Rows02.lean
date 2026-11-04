/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01669Affine

/-!
# Original leaf 01669 — Rows02

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01669.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01669_w_row020 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row020 leaf01669_w_affine)
theorem leaf01669_w_row020_weighted : leaf01669_w_row020=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row020 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row020_identity : leaf01669_w_row020=NestedInteger.coefficientFrom 88 20 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 20 0 leaf01669_w_affine leaf01669_w_row020 IntegerBernsteinWeights88.row020 (IntegerBernsteinTable.checked (n := 2) 88 20 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row020 leaf01669_w_affine_length IntegerBernsteinWeights88.row020_identity) leaf01669_w_row020_weighted
theorem leaf01669_w_row020_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row020=true := by decide +kernel
#print axioms leaf01669_w_row020_weighted
#print axioms leaf01669_w_row020_identity
#print axioms leaf01669_w_row020_positive
def leaf01669_w_row021 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row021 leaf01669_w_affine)
theorem leaf01669_w_row021_weighted : leaf01669_w_row021=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row021 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row021_identity : leaf01669_w_row021=NestedInteger.coefficientFrom 88 21 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 21 0 leaf01669_w_affine leaf01669_w_row021 IntegerBernsteinWeights88.row021 (IntegerBernsteinTable.checked (n := 2) 88 21 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row021 leaf01669_w_affine_length IntegerBernsteinWeights88.row021_identity) leaf01669_w_row021_weighted
theorem leaf01669_w_row021_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row021=true := by decide +kernel
#print axioms leaf01669_w_row021_weighted
#print axioms leaf01669_w_row021_identity
#print axioms leaf01669_w_row021_positive
def leaf01669_w_row022 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row022 leaf01669_w_affine)
theorem leaf01669_w_row022_weighted : leaf01669_w_row022=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row022 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row022_identity : leaf01669_w_row022=NestedInteger.coefficientFrom 88 22 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 22 0 leaf01669_w_affine leaf01669_w_row022 IntegerBernsteinWeights88.row022 (IntegerBernsteinTable.checked (n := 2) 88 22 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row022 leaf01669_w_affine_length IntegerBernsteinWeights88.row022_identity) leaf01669_w_row022_weighted
theorem leaf01669_w_row022_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row022=true := by decide +kernel
#print axioms leaf01669_w_row022_weighted
#print axioms leaf01669_w_row022_identity
#print axioms leaf01669_w_row022_positive
def leaf01669_w_row023 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row023 leaf01669_w_affine)
theorem leaf01669_w_row023_weighted : leaf01669_w_row023=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row023 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row023_identity : leaf01669_w_row023=NestedInteger.coefficientFrom 88 23 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 23 0 leaf01669_w_affine leaf01669_w_row023 IntegerBernsteinWeights88.row023 (IntegerBernsteinTable.checked (n := 2) 88 23 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row023 leaf01669_w_affine_length IntegerBernsteinWeights88.row023_identity) leaf01669_w_row023_weighted
theorem leaf01669_w_row023_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row023=true := by decide +kernel
#print axioms leaf01669_w_row023_weighted
#print axioms leaf01669_w_row023_identity
#print axioms leaf01669_w_row023_positive
def leaf01669_w_row024 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01669_w_affine)
theorem leaf01669_w_row024_weighted : leaf01669_w_row024=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row024_identity : leaf01669_w_row024=NestedInteger.coefficientFrom 88 24 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 24 0 leaf01669_w_affine leaf01669_w_row024 IntegerBernsteinWeights88.row024 (IntegerBernsteinTable.checked (n := 2) 88 24 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row024 leaf01669_w_affine_length IntegerBernsteinWeights88.row024_identity) leaf01669_w_row024_weighted
theorem leaf01669_w_row024_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row024=true := by decide +kernel
#print axioms leaf01669_w_row024_weighted
#print axioms leaf01669_w_row024_identity
#print axioms leaf01669_w_row024_positive
def leaf01669_w_row025 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row025 leaf01669_w_affine)
theorem leaf01669_w_row025_weighted : leaf01669_w_row025=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row025 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row025_identity : leaf01669_w_row025=NestedInteger.coefficientFrom 88 25 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 25 0 leaf01669_w_affine leaf01669_w_row025 IntegerBernsteinWeights88.row025 (IntegerBernsteinTable.checked (n := 2) 88 25 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row025 leaf01669_w_affine_length IntegerBernsteinWeights88.row025_identity) leaf01669_w_row025_weighted
theorem leaf01669_w_row025_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row025=true := by decide +kernel
#print axioms leaf01669_w_row025_weighted
#print axioms leaf01669_w_row025_identity
#print axioms leaf01669_w_row025_positive
def leaf01669_w_row026 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf01669_w_affine)
theorem leaf01669_w_row026_weighted : leaf01669_w_row026=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row026_identity : leaf01669_w_row026=NestedInteger.coefficientFrom 88 26 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 26 0 leaf01669_w_affine leaf01669_w_row026 IntegerBernsteinWeights88.row026 (IntegerBernsteinTable.checked (n := 2) 88 26 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row026 leaf01669_w_affine_length IntegerBernsteinWeights88.row026_identity) leaf01669_w_row026_weighted
theorem leaf01669_w_row026_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row026=true := by decide +kernel
#print axioms leaf01669_w_row026_weighted
#print axioms leaf01669_w_row026_identity
#print axioms leaf01669_w_row026_positive
def leaf01669_w_row027 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row027 leaf01669_w_affine)
theorem leaf01669_w_row027_weighted : leaf01669_w_row027=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row027 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row027_identity : leaf01669_w_row027=NestedInteger.coefficientFrom 88 27 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 27 0 leaf01669_w_affine leaf01669_w_row027 IntegerBernsteinWeights88.row027 (IntegerBernsteinTable.checked (n := 2) 88 27 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row027 leaf01669_w_affine_length IntegerBernsteinWeights88.row027_identity) leaf01669_w_row027_weighted
theorem leaf01669_w_row027_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row027=true := by decide +kernel
#print axioms leaf01669_w_row027_weighted
#print axioms leaf01669_w_row027_identity
#print axioms leaf01669_w_row027_positive
def leaf01669_w_row028 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row028 leaf01669_w_affine)
theorem leaf01669_w_row028_weighted : leaf01669_w_row028=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row028 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row028_identity : leaf01669_w_row028=NestedInteger.coefficientFrom 88 28 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 28 0 leaf01669_w_affine leaf01669_w_row028 IntegerBernsteinWeights88.row028 (IntegerBernsteinTable.checked (n := 2) 88 28 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row028 leaf01669_w_affine_length IntegerBernsteinWeights88.row028_identity) leaf01669_w_row028_weighted
theorem leaf01669_w_row028_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row028=true := by decide +kernel
#print axioms leaf01669_w_row028_weighted
#print axioms leaf01669_w_row028_identity
#print axioms leaf01669_w_row028_positive
def leaf01669_w_row029 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row029 leaf01669_w_affine)
theorem leaf01669_w_row029_weighted : leaf01669_w_row029=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row029 leaf01669_w_affine := by decide +kernel
theorem leaf01669_w_row029_identity : leaf01669_w_row029=NestedInteger.coefficientFrom 88 29 0 leaf01669_w_affine :=
  IntegerWeightedBernstein.checked 88 29 0 leaf01669_w_affine leaf01669_w_row029 IntegerBernsteinWeights88.row029 (IntegerBernsteinTable.checked (n := 2) 88 29 0 89 leaf01669_w_affine IntegerBernsteinWeights88.row029 leaf01669_w_affine_length IntegerBernsteinWeights88.row029_identity) leaf01669_w_row029_weighted
theorem leaf01669_w_row029_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01669_w_row029=true := by decide +kernel
#print axioms leaf01669_w_row029_weighted
#print axioms leaf01669_w_row029_identity
#print axioms leaf01669_w_row029_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
