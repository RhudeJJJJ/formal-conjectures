/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01342RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01342_w_row068 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row068 leaf01342_w_affine)
theorem leaf01342_w_row068_weighted : leaf01342_w_row068=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row068 leaf01342_w_affine := by decide +kernel
theorem leaf01342_w_row068_identity : leaf01342_w_row068=NestedInteger.coefficientFrom 88 68 0 leaf01342_w_affine :=
  IntegerWeightedBernstein.checked 88 68 0 leaf01342_w_affine leaf01342_w_row068 IntegerBernsteinWeights88.row068 (IntegerBernsteinTable.checked (n := 2) 88 68 0 89 leaf01342_w_affine IntegerBernsteinWeights88.row068 leaf01342_w_affine_length IntegerBernsteinWeights88.row068_identity) leaf01342_w_row068_weighted
theorem leaf01342_w_row068_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01342_w_row068=true := by decide +kernel
#print axioms leaf01342_w_row068_weighted
#print axioms leaf01342_w_row068_identity
#print axioms leaf01342_w_row068_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
