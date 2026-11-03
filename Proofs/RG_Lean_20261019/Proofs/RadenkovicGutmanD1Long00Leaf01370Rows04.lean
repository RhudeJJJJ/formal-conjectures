/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01370Affine

/-!
# Bernstein row certificates 4 for leaf 01370

These declarations retain the original polynomial data and proof bodies.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01370.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01370_w_row040 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row040 leaf01370_w_affine)
theorem leaf01370_w_row040_weighted : leaf01370_w_row040=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row040 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row040_identity : leaf01370_w_row040=NestedInteger.coefficientFrom 88 40 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 40 0 leaf01370_w_affine leaf01370_w_row040 IntegerBernsteinWeights88.row040 (IntegerBernsteinTable.checked (n := 2) 88 40 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row040 leaf01370_w_affine_length IntegerBernsteinWeights88.row040_identity) leaf01370_w_row040_weighted
theorem leaf01370_w_row040_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row040=true := by decide +kernel
#print axioms leaf01370_w_row040_weighted
#print axioms leaf01370_w_row040_identity
#print axioms leaf01370_w_row040_positive
def leaf01370_w_row041 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row041 leaf01370_w_affine)
theorem leaf01370_w_row041_weighted : leaf01370_w_row041=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row041 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row041_identity : leaf01370_w_row041=NestedInteger.coefficientFrom 88 41 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 41 0 leaf01370_w_affine leaf01370_w_row041 IntegerBernsteinWeights88.row041 (IntegerBernsteinTable.checked (n := 2) 88 41 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row041 leaf01370_w_affine_length IntegerBernsteinWeights88.row041_identity) leaf01370_w_row041_weighted
theorem leaf01370_w_row041_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row041=true := by decide +kernel
#print axioms leaf01370_w_row041_weighted
#print axioms leaf01370_w_row041_identity
#print axioms leaf01370_w_row041_positive
def leaf01370_w_row042 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row042 leaf01370_w_affine)
theorem leaf01370_w_row042_weighted : leaf01370_w_row042=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row042 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row042_identity : leaf01370_w_row042=NestedInteger.coefficientFrom 88 42 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 42 0 leaf01370_w_affine leaf01370_w_row042 IntegerBernsteinWeights88.row042 (IntegerBernsteinTable.checked (n := 2) 88 42 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row042 leaf01370_w_affine_length IntegerBernsteinWeights88.row042_identity) leaf01370_w_row042_weighted
theorem leaf01370_w_row042_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row042=true := by decide +kernel
#print axioms leaf01370_w_row042_weighted
#print axioms leaf01370_w_row042_identity
#print axioms leaf01370_w_row042_positive
def leaf01370_w_row043 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row043 leaf01370_w_affine)
theorem leaf01370_w_row043_weighted : leaf01370_w_row043=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row043 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row043_identity : leaf01370_w_row043=NestedInteger.coefficientFrom 88 43 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 43 0 leaf01370_w_affine leaf01370_w_row043 IntegerBernsteinWeights88.row043 (IntegerBernsteinTable.checked (n := 2) 88 43 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row043 leaf01370_w_affine_length IntegerBernsteinWeights88.row043_identity) leaf01370_w_row043_weighted
theorem leaf01370_w_row043_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row043=true := by decide +kernel
#print axioms leaf01370_w_row043_weighted
#print axioms leaf01370_w_row043_identity
#print axioms leaf01370_w_row043_positive
def leaf01370_w_row044 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row044 leaf01370_w_affine)
theorem leaf01370_w_row044_weighted : leaf01370_w_row044=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row044 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row044_identity : leaf01370_w_row044=NestedInteger.coefficientFrom 88 44 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 44 0 leaf01370_w_affine leaf01370_w_row044 IntegerBernsteinWeights88.row044 (IntegerBernsteinTable.checked (n := 2) 88 44 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row044 leaf01370_w_affine_length IntegerBernsteinWeights88.row044_identity) leaf01370_w_row044_weighted
theorem leaf01370_w_row044_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row044=true := by decide +kernel
#print axioms leaf01370_w_row044_weighted
#print axioms leaf01370_w_row044_identity
#print axioms leaf01370_w_row044_positive
def leaf01370_w_row045 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row045 leaf01370_w_affine)
theorem leaf01370_w_row045_weighted : leaf01370_w_row045=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row045 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row045_identity : leaf01370_w_row045=NestedInteger.coefficientFrom 88 45 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 45 0 leaf01370_w_affine leaf01370_w_row045 IntegerBernsteinWeights88.row045 (IntegerBernsteinTable.checked (n := 2) 88 45 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row045 leaf01370_w_affine_length IntegerBernsteinWeights88.row045_identity) leaf01370_w_row045_weighted
theorem leaf01370_w_row045_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row045=true := by decide +kernel
#print axioms leaf01370_w_row045_weighted
#print axioms leaf01370_w_row045_identity
#print axioms leaf01370_w_row045_positive
def leaf01370_w_row046 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf01370_w_affine)
theorem leaf01370_w_row046_weighted : leaf01370_w_row046=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row046_identity : leaf01370_w_row046=NestedInteger.coefficientFrom 88 46 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 46 0 leaf01370_w_affine leaf01370_w_row046 IntegerBernsteinWeights88.row046 (IntegerBernsteinTable.checked (n := 2) 88 46 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row046 leaf01370_w_affine_length IntegerBernsteinWeights88.row046_identity) leaf01370_w_row046_weighted
theorem leaf01370_w_row046_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row046=true := by decide +kernel
#print axioms leaf01370_w_row046_weighted
#print axioms leaf01370_w_row046_identity
#print axioms leaf01370_w_row046_positive
def leaf01370_w_row047 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row047 leaf01370_w_affine)
theorem leaf01370_w_row047_weighted : leaf01370_w_row047=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row047 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row047_identity : leaf01370_w_row047=NestedInteger.coefficientFrom 88 47 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 47 0 leaf01370_w_affine leaf01370_w_row047 IntegerBernsteinWeights88.row047 (IntegerBernsteinTable.checked (n := 2) 88 47 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row047 leaf01370_w_affine_length IntegerBernsteinWeights88.row047_identity) leaf01370_w_row047_weighted
theorem leaf01370_w_row047_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row047=true := by decide +kernel
#print axioms leaf01370_w_row047_weighted
#print axioms leaf01370_w_row047_identity
#print axioms leaf01370_w_row047_positive
def leaf01370_w_row048 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row048 leaf01370_w_affine)
theorem leaf01370_w_row048_weighted : leaf01370_w_row048=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row048 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row048_identity : leaf01370_w_row048=NestedInteger.coefficientFrom 88 48 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 48 0 leaf01370_w_affine leaf01370_w_row048 IntegerBernsteinWeights88.row048 (IntegerBernsteinTable.checked (n := 2) 88 48 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row048 leaf01370_w_affine_length IntegerBernsteinWeights88.row048_identity) leaf01370_w_row048_weighted
theorem leaf01370_w_row048_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row048=true := by decide +kernel
#print axioms leaf01370_w_row048_weighted
#print axioms leaf01370_w_row048_identity
#print axioms leaf01370_w_row048_positive
def leaf01370_w_row049 : NestedInteger.Poly 2 := rg_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row049 leaf01370_w_affine)
theorem leaf01370_w_row049_weighted : leaf01370_w_row049=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row049 leaf01370_w_affine := by decide +kernel
theorem leaf01370_w_row049_identity : leaf01370_w_row049=NestedInteger.coefficientFrom 88 49 0 leaf01370_w_affine :=
  IntegerWeightedBernstein.checked 88 49 0 leaf01370_w_affine leaf01370_w_row049 IntegerBernsteinWeights88.row049 (IntegerBernsteinTable.checked (n := 2) 88 49 0 89 leaf01370_w_affine IntegerBernsteinWeights88.row049 leaf01370_w_affine_length IntegerBernsteinWeights88.row049_identity) leaf01370_w_row049_weighted
theorem leaf01370_w_row049_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01370_w_row049=true := by decide +kernel
#print axioms leaf01370_w_row049_weighted
#print axioms leaf01370_w_row049_identity
#print axioms leaf01370_w_row049_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
