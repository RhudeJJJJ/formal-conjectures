/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260BoundedGroupedCompositionalRepairJoins02
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row080 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row080 leaf01260_w_affine)
theorem leaf01260_w_row080_weighted : leaf01260_w_row080=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row080 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row080_identity : leaf01260_w_row080=NestedInteger.coefficientFrom 88 80 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 80 0 leaf01260_w_affine leaf01260_w_row080 IntegerBernsteinWeights88.row080 (IntegerBernsteinTable.checked (n := 2) 88 80 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row080 leaf01260_w_affine_length IntegerBernsteinWeights88.row080_identity) leaf01260_w_row080_weighted
theorem leaf01260_w_row080_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row080=true := by decide +kernel
#print axioms leaf01260_w_row080_weighted
#print axioms leaf01260_w_row080_identity
#print axioms leaf01260_w_row080_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row081 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row081 leaf01260_w_affine)
theorem leaf01260_w_row081_weighted : leaf01260_w_row081=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row081 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row081_identity : leaf01260_w_row081=NestedInteger.coefficientFrom 88 81 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 81 0 leaf01260_w_affine leaf01260_w_row081 IntegerBernsteinWeights88.row081 (IntegerBernsteinTable.checked (n := 2) 88 81 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row081 leaf01260_w_affine_length IntegerBernsteinWeights88.row081_identity) leaf01260_w_row081_weighted
theorem leaf01260_w_row081_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row081=true := by decide +kernel
#print axioms leaf01260_w_row081_weighted
#print axioms leaf01260_w_row081_identity
#print axioms leaf01260_w_row081_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row082 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row082 leaf01260_w_affine)
theorem leaf01260_w_row082_weighted : leaf01260_w_row082=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row082 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row082_identity : leaf01260_w_row082=NestedInteger.coefficientFrom 88 82 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 82 0 leaf01260_w_affine leaf01260_w_row082 IntegerBernsteinWeights88.row082 (IntegerBernsteinTable.checked (n := 2) 88 82 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row082 leaf01260_w_affine_length IntegerBernsteinWeights88.row082_identity) leaf01260_w_row082_weighted
theorem leaf01260_w_row082_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row082=true := by decide +kernel
#print axioms leaf01260_w_row082_weighted
#print axioms leaf01260_w_row082_identity
#print axioms leaf01260_w_row082_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row083 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row083 leaf01260_w_affine)
theorem leaf01260_w_row083_weighted : leaf01260_w_row083=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row083 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row083_identity : leaf01260_w_row083=NestedInteger.coefficientFrom 88 83 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 83 0 leaf01260_w_affine leaf01260_w_row083 IntegerBernsteinWeights88.row083 (IntegerBernsteinTable.checked (n := 2) 88 83 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row083 leaf01260_w_affine_length IntegerBernsteinWeights88.row083_identity) leaf01260_w_row083_weighted
theorem leaf01260_w_row083_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row083=true := by decide +kernel
#print axioms leaf01260_w_row083_weighted
#print axioms leaf01260_w_row083_identity
#print axioms leaf01260_w_row083_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row084 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row084 leaf01260_w_affine)
theorem leaf01260_w_row084_weighted : leaf01260_w_row084=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row084 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row084_identity : leaf01260_w_row084=NestedInteger.coefficientFrom 88 84 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 84 0 leaf01260_w_affine leaf01260_w_row084 IntegerBernsteinWeights88.row084 (IntegerBernsteinTable.checked (n := 2) 88 84 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row084 leaf01260_w_affine_length IntegerBernsteinWeights88.row084_identity) leaf01260_w_row084_weighted
theorem leaf01260_w_row084_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row084=true := by decide +kernel
#print axioms leaf01260_w_row084_weighted
#print axioms leaf01260_w_row084_identity
#print axioms leaf01260_w_row084_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row085 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row085 leaf01260_w_affine)
theorem leaf01260_w_row085_weighted : leaf01260_w_row085=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row085 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row085_identity : leaf01260_w_row085=NestedInteger.coefficientFrom 88 85 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 85 0 leaf01260_w_affine leaf01260_w_row085 IntegerBernsteinWeights88.row085 (IntegerBernsteinTable.checked (n := 2) 88 85 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row085 leaf01260_w_affine_length IntegerBernsteinWeights88.row085_identity) leaf01260_w_row085_weighted
theorem leaf01260_w_row085_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row085=true := by decide +kernel
#print axioms leaf01260_w_row085_weighted
#print axioms leaf01260_w_row085_identity
#print axioms leaf01260_w_row085_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row086 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row086 leaf01260_w_affine)
theorem leaf01260_w_row086_weighted : leaf01260_w_row086=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row086 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row086_identity : leaf01260_w_row086=NestedInteger.coefficientFrom 88 86 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 86 0 leaf01260_w_affine leaf01260_w_row086 IntegerBernsteinWeights88.row086 (IntegerBernsteinTable.checked (n := 2) 88 86 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row086 leaf01260_w_affine_length IntegerBernsteinWeights88.row086_identity) leaf01260_w_row086_weighted
theorem leaf01260_w_row086_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row086=true := by decide +kernel
#print axioms leaf01260_w_row086_weighted
#print axioms leaf01260_w_row086_identity
#print axioms leaf01260_w_row086_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row087 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row087 leaf01260_w_affine)
theorem leaf01260_w_row087_weighted : leaf01260_w_row087=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row087 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row087_identity : leaf01260_w_row087=NestedInteger.coefficientFrom 88 87 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 87 0 leaf01260_w_affine leaf01260_w_row087 IntegerBernsteinWeights88.row087 (IntegerBernsteinTable.checked (n := 2) 88 87 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row087 leaf01260_w_affine_length IntegerBernsteinWeights88.row087_identity) leaf01260_w_row087_weighted
theorem leaf01260_w_row087_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row087=true := by decide +kernel
#print axioms leaf01260_w_row087_weighted
#print axioms leaf01260_w_row087_identity
#print axioms leaf01260_w_row087_positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01260_w_row088 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row088 leaf01260_w_affine)
theorem leaf01260_w_row088_weighted : leaf01260_w_row088=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row088 leaf01260_w_affine := by decide +kernel
theorem leaf01260_w_row088_identity : leaf01260_w_row088=NestedInteger.coefficientFrom 88 88 0 leaf01260_w_affine :=
  IntegerWeightedBernstein.checked 88 88 0 leaf01260_w_affine leaf01260_w_row088 IntegerBernsteinWeights88.row088 (IntegerBernsteinTable.checked (n := 2) 88 88 0 89 leaf01260_w_affine IntegerBernsteinWeights88.row088 leaf01260_w_affine_length IntegerBernsteinWeights88.row088_identity) leaf01260_w_row088_weighted
theorem leaf01260_w_row088_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01260_w_row088=true := by decide +kernel
#print axioms leaf01260_w_row088_weighted
#print axioms leaf01260_w_row088_identity
#print axioms leaf01260_w_row088_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
