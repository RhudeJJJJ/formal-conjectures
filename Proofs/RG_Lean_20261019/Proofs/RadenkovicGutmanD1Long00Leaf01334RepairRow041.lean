/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01334RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01334_w_row041 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row041 leaf01334_w_affine)
theorem leaf01334_w_row041_weighted : leaf01334_w_row041=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row041 leaf01334_w_affine := by decide +kernel
theorem leaf01334_w_row041_identity : leaf01334_w_row041=NestedInteger.coefficientFrom 88 41 0 leaf01334_w_affine :=
  IntegerWeightedBernstein.checked 88 41 0 leaf01334_w_affine leaf01334_w_row041 IntegerBernsteinWeights88.row041 (IntegerBernsteinTable.checked (n := 2) 88 41 0 89 leaf01334_w_affine IntegerBernsteinWeights88.row041 leaf01334_w_affine_length IntegerBernsteinWeights88.row041_identity) leaf01334_w_row041_weighted
theorem leaf01334_w_row041_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01334_w_row041=true := by decide +kernel
#print axioms leaf01334_w_row041_weighted
#print axioms leaf01334_w_row041_identity
#print axioms leaf01334_w_row041_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
