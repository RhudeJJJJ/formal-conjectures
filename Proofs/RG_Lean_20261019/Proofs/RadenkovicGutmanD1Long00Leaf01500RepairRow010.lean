/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01500RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01500_w_row010 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row010 leaf01500_w_affine)
theorem leaf01500_w_row010_weighted : leaf01500_w_row010=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row010 leaf01500_w_affine := by decide +kernel
theorem leaf01500_w_row010_identity : leaf01500_w_row010=NestedInteger.coefficientFrom 88 10 0 leaf01500_w_affine :=
  IntegerWeightedBernstein.checked 88 10 0 leaf01500_w_affine leaf01500_w_row010 IntegerBernsteinWeights88.row010 (IntegerBernsteinTable.checked (n := 2) 88 10 0 89 leaf01500_w_affine IntegerBernsteinWeights88.row010 leaf01500_w_affine_length IntegerBernsteinWeights88.row010_identity) leaf01500_w_row010_weighted
theorem leaf01500_w_row010_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01500_w_row010=true := by decide +kernel
#print axioms leaf01500_w_row010_weighted
#print axioms leaf01500_w_row010_identity
#print axioms leaf01500_w_row010_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
