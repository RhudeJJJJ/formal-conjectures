/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01515RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01515_w_row044 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row044 leaf01515_w_affine)
theorem leaf01515_w_row044_weighted : leaf01515_w_row044=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row044 leaf01515_w_affine := by decide +kernel
theorem leaf01515_w_row044_identity : leaf01515_w_row044=NestedInteger.coefficientFrom 88 44 0 leaf01515_w_affine :=
  IntegerWeightedBernstein.checked 88 44 0 leaf01515_w_affine leaf01515_w_row044 IntegerBernsteinWeights88.row044 (IntegerBernsteinTable.checked (n := 2) 88 44 0 89 leaf01515_w_affine IntegerBernsteinWeights88.row044 leaf01515_w_affine_length IntegerBernsteinWeights88.row044_identity) leaf01515_w_row044_weighted
theorem leaf01515_w_row044_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01515_w_row044=true := by decide +kernel
#print axioms leaf01515_w_row044_weighted
#print axioms leaf01515_w_row044_identity
#print axioms leaf01515_w_row044_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
