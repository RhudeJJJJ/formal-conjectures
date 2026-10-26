/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01615CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01615_w_row011 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row011 leaf01615_w_affine)
theorem leaf01615_w_row011_weighted : leaf01615_w_row011=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row011 leaf01615_w_affine := by decide +kernel
theorem leaf01615_w_row011_identity : leaf01615_w_row011=NestedInteger.coefficientFrom 88 11 0 leaf01615_w_affine :=
  IntegerWeightedBernstein.checked 88 11 0 leaf01615_w_affine leaf01615_w_row011 IntegerBernsteinWeights88.row011 (IntegerBernsteinTable.checked (n := 2) 88 11 0 89 leaf01615_w_affine IntegerBernsteinWeights88.row011 leaf01615_w_affine_length IntegerBernsteinWeights88.row011_identity) leaf01615_w_row011_weighted
theorem leaf01615_w_row011_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01615_w_row011=true := by decide +kernel
#print axioms leaf01615_w_row011_weighted
#print axioms leaf01615_w_row011_identity
#print axioms leaf01615_w_row011_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
