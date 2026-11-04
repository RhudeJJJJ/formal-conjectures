/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01666Affine

/-!
# Original leaf 01666 — Rows00

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01666.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01666_w_row000 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row000 leaf01666_w_affine)
theorem leaf01666_w_row000_weighted : leaf01666_w_row000=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row000 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row000_identity : leaf01666_w_row000=NestedInteger.coefficientFrom 88 0 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 0 0 leaf01666_w_affine leaf01666_w_row000 IntegerBernsteinWeights88.row000 (IntegerBernsteinTable.checked (n := 2) 88 0 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row000 leaf01666_w_affine_length IntegerBernsteinWeights88.row000_identity) leaf01666_w_row000_weighted
theorem leaf01666_w_row000_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row000=true := by decide +kernel
#print axioms leaf01666_w_row000_weighted
#print axioms leaf01666_w_row000_identity
#print axioms leaf01666_w_row000_positive
def leaf01666_w_row001 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row001 leaf01666_w_affine)
theorem leaf01666_w_row001_weighted : leaf01666_w_row001=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row001 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row001_identity : leaf01666_w_row001=NestedInteger.coefficientFrom 88 1 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 1 0 leaf01666_w_affine leaf01666_w_row001 IntegerBernsteinWeights88.row001 (IntegerBernsteinTable.checked (n := 2) 88 1 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row001 leaf01666_w_affine_length IntegerBernsteinWeights88.row001_identity) leaf01666_w_row001_weighted
theorem leaf01666_w_row001_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row001=true := by decide +kernel
#print axioms leaf01666_w_row001_weighted
#print axioms leaf01666_w_row001_identity
#print axioms leaf01666_w_row001_positive
def leaf01666_w_row002 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row002 leaf01666_w_affine)
theorem leaf01666_w_row002_weighted : leaf01666_w_row002=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row002 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row002_identity : leaf01666_w_row002=NestedInteger.coefficientFrom 88 2 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 2 0 leaf01666_w_affine leaf01666_w_row002 IntegerBernsteinWeights88.row002 (IntegerBernsteinTable.checked (n := 2) 88 2 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row002 leaf01666_w_affine_length IntegerBernsteinWeights88.row002_identity) leaf01666_w_row002_weighted
theorem leaf01666_w_row002_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row002=true := by decide +kernel
#print axioms leaf01666_w_row002_weighted
#print axioms leaf01666_w_row002_identity
#print axioms leaf01666_w_row002_positive
def leaf01666_w_row003 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row003 leaf01666_w_affine)
theorem leaf01666_w_row003_weighted : leaf01666_w_row003=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row003 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row003_identity : leaf01666_w_row003=NestedInteger.coefficientFrom 88 3 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 3 0 leaf01666_w_affine leaf01666_w_row003 IntegerBernsteinWeights88.row003 (IntegerBernsteinTable.checked (n := 2) 88 3 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row003 leaf01666_w_affine_length IntegerBernsteinWeights88.row003_identity) leaf01666_w_row003_weighted
theorem leaf01666_w_row003_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row003=true := by decide +kernel
#print axioms leaf01666_w_row003_weighted
#print axioms leaf01666_w_row003_identity
#print axioms leaf01666_w_row003_positive
def leaf01666_w_row004 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row004 leaf01666_w_affine)
theorem leaf01666_w_row004_weighted : leaf01666_w_row004=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row004 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row004_identity : leaf01666_w_row004=NestedInteger.coefficientFrom 88 4 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 4 0 leaf01666_w_affine leaf01666_w_row004 IntegerBernsteinWeights88.row004 (IntegerBernsteinTable.checked (n := 2) 88 4 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row004 leaf01666_w_affine_length IntegerBernsteinWeights88.row004_identity) leaf01666_w_row004_weighted
theorem leaf01666_w_row004_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row004=true := by decide +kernel
#print axioms leaf01666_w_row004_weighted
#print axioms leaf01666_w_row004_identity
#print axioms leaf01666_w_row004_positive
def leaf01666_w_row005 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row005 leaf01666_w_affine)
theorem leaf01666_w_row005_weighted : leaf01666_w_row005=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row005 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row005_identity : leaf01666_w_row005=NestedInteger.coefficientFrom 88 5 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 5 0 leaf01666_w_affine leaf01666_w_row005 IntegerBernsteinWeights88.row005 (IntegerBernsteinTable.checked (n := 2) 88 5 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row005 leaf01666_w_affine_length IntegerBernsteinWeights88.row005_identity) leaf01666_w_row005_weighted
theorem leaf01666_w_row005_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row005=true := by decide +kernel
#print axioms leaf01666_w_row005_weighted
#print axioms leaf01666_w_row005_identity
#print axioms leaf01666_w_row005_positive
def leaf01666_w_row006 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row006 leaf01666_w_affine)
theorem leaf01666_w_row006_weighted : leaf01666_w_row006=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row006 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row006_identity : leaf01666_w_row006=NestedInteger.coefficientFrom 88 6 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 6 0 leaf01666_w_affine leaf01666_w_row006 IntegerBernsteinWeights88.row006 (IntegerBernsteinTable.checked (n := 2) 88 6 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row006 leaf01666_w_affine_length IntegerBernsteinWeights88.row006_identity) leaf01666_w_row006_weighted
theorem leaf01666_w_row006_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row006=true := by decide +kernel
#print axioms leaf01666_w_row006_weighted
#print axioms leaf01666_w_row006_identity
#print axioms leaf01666_w_row006_positive
def leaf01666_w_row007 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row007 leaf01666_w_affine)
theorem leaf01666_w_row007_weighted : leaf01666_w_row007=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row007 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row007_identity : leaf01666_w_row007=NestedInteger.coefficientFrom 88 7 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 7 0 leaf01666_w_affine leaf01666_w_row007 IntegerBernsteinWeights88.row007 (IntegerBernsteinTable.checked (n := 2) 88 7 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row007 leaf01666_w_affine_length IntegerBernsteinWeights88.row007_identity) leaf01666_w_row007_weighted
theorem leaf01666_w_row007_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row007=true := by decide +kernel
#print axioms leaf01666_w_row007_weighted
#print axioms leaf01666_w_row007_identity
#print axioms leaf01666_w_row007_positive
def leaf01666_w_row008 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row008 leaf01666_w_affine)
theorem leaf01666_w_row008_weighted : leaf01666_w_row008=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row008 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row008_identity : leaf01666_w_row008=NestedInteger.coefficientFrom 88 8 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 8 0 leaf01666_w_affine leaf01666_w_row008 IntegerBernsteinWeights88.row008 (IntegerBernsteinTable.checked (n := 2) 88 8 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row008 leaf01666_w_affine_length IntegerBernsteinWeights88.row008_identity) leaf01666_w_row008_weighted
theorem leaf01666_w_row008_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row008=true := by decide +kernel
#print axioms leaf01666_w_row008_weighted
#print axioms leaf01666_w_row008_identity
#print axioms leaf01666_w_row008_positive
def leaf01666_w_row009 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row009 leaf01666_w_affine)
theorem leaf01666_w_row009_weighted : leaf01666_w_row009=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row009 leaf01666_w_affine := by decide +kernel
theorem leaf01666_w_row009_identity : leaf01666_w_row009=NestedInteger.coefficientFrom 88 9 0 leaf01666_w_affine :=
  IntegerWeightedBernstein.checked 88 9 0 leaf01666_w_affine leaf01666_w_row009 IntegerBernsteinWeights88.row009 (IntegerBernsteinTable.checked (n := 2) 88 9 0 89 leaf01666_w_affine IntegerBernsteinWeights88.row009 leaf01666_w_affine_length IntegerBernsteinWeights88.row009_identity) leaf01666_w_row009_weighted
theorem leaf01666_w_row009_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01666_w_row009=true := by decide +kernel
#print axioms leaf01666_w_row009_weighted
#print axioms leaf01666_w_row009_identity
#print axioms leaf01666_w_row009_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
