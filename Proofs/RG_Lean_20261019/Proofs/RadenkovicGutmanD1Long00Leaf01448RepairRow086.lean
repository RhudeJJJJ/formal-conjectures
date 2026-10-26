/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01448RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01448_w_row086 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row086 leaf01448_w_affine)
theorem leaf01448_w_row086_weighted : leaf01448_w_row086=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row086 leaf01448_w_affine := by decide +kernel
theorem leaf01448_w_row086_identity : leaf01448_w_row086=NestedInteger.coefficientFrom 88 86 0 leaf01448_w_affine :=
  IntegerWeightedBernstein.checked 88 86 0 leaf01448_w_affine leaf01448_w_row086 IntegerBernsteinWeights88.row086 (IntegerBernsteinTable.checked (n := 2) 88 86 0 89 leaf01448_w_affine IntegerBernsteinWeights88.row086 leaf01448_w_affine_length IntegerBernsteinWeights88.row086_identity) leaf01448_w_row086_weighted
theorem leaf01448_w_row086_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01448_w_row086=true := by decide +kernel
#print axioms leaf01448_w_row086_weighted
#print axioms leaf01448_w_row086_identity
#print axioms leaf01448_w_row086_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
