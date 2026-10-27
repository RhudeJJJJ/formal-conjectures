/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01275RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01275_w_row087 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row087 leaf01275_w_affine)
theorem leaf01275_w_row087_weighted : leaf01275_w_row087=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row087 leaf01275_w_affine := by decide +kernel
theorem leaf01275_w_row087_identity : leaf01275_w_row087=NestedInteger.coefficientFrom 88 87 0 leaf01275_w_affine :=
  IntegerWeightedBernstein.checked 88 87 0 leaf01275_w_affine leaf01275_w_row087 IntegerBernsteinWeights88.row087 (IntegerBernsteinTable.checked (n := 2) 88 87 0 89 leaf01275_w_affine IntegerBernsteinWeights88.row087 leaf01275_w_affine_length IntegerBernsteinWeights88.row087_identity) leaf01275_w_row087_weighted
theorem leaf01275_w_row087_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01275_w_row087=true := by decide +kernel
#print axioms leaf01275_w_row087_weighted
#print axioms leaf01275_w_row087_identity
#print axioms leaf01275_w_row087_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
