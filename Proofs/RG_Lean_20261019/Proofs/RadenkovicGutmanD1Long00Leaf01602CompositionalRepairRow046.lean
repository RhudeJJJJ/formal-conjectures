/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01602CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01602_w_row046 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf01602_w_affine)
theorem leaf01602_w_row046_weighted : leaf01602_w_row046=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row046 leaf01602_w_affine := by decide +kernel
theorem leaf01602_w_row046_identity : leaf01602_w_row046=NestedInteger.coefficientFrom 88 46 0 leaf01602_w_affine :=
  IntegerWeightedBernstein.checked 88 46 0 leaf01602_w_affine leaf01602_w_row046 IntegerBernsteinWeights88.row046 (IntegerBernsteinTable.checked (n := 2) 88 46 0 89 leaf01602_w_affine IntegerBernsteinWeights88.row046 leaf01602_w_affine_length IntegerBernsteinWeights88.row046_identity) leaf01602_w_row046_weighted
theorem leaf01602_w_row046_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01602_w_row046=true := by decide +kernel
#print axioms leaf01602_w_row046_weighted
#print axioms leaf01602_w_row046_identity
#print axioms leaf01602_w_row046_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
