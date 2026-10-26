/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01303RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01303_w_row016 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row016 leaf01303_w_affine)
theorem leaf01303_w_row016_weighted : leaf01303_w_row016=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row016 leaf01303_w_affine := by decide +kernel
theorem leaf01303_w_row016_identity : leaf01303_w_row016=NestedInteger.coefficientFrom 88 16 0 leaf01303_w_affine :=
  IntegerWeightedBernstein.checked 88 16 0 leaf01303_w_affine leaf01303_w_row016 IntegerBernsteinWeights88.row016 (IntegerBernsteinTable.checked (n := 2) 88 16 0 89 leaf01303_w_affine IntegerBernsteinWeights88.row016 leaf01303_w_affine_length IntegerBernsteinWeights88.row016_identity) leaf01303_w_row016_weighted
theorem leaf01303_w_row016_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01303_w_row016=true := by decide +kernel
#print axioms leaf01303_w_row016_weighted
#print axioms leaf01303_w_row016_identity
#print axioms leaf01303_w_row016_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
