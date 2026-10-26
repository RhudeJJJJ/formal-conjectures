/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01328RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01328_w_row032 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01328_w_affine)
theorem leaf01328_w_row032_weighted : leaf01328_w_row032=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row032 leaf01328_w_affine := by decide +kernel
theorem leaf01328_w_row032_identity : leaf01328_w_row032=NestedInteger.coefficientFrom 88 32 0 leaf01328_w_affine :=
  IntegerWeightedBernstein.checked 88 32 0 leaf01328_w_affine leaf01328_w_row032 IntegerBernsteinWeights88.row032 (IntegerBernsteinTable.checked (n := 2) 88 32 0 89 leaf01328_w_affine IntegerBernsteinWeights88.row032 leaf01328_w_affine_length IntegerBernsteinWeights88.row032_identity) leaf01328_w_row032_weighted
theorem leaf01328_w_row032_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01328_w_row032=true := by decide +kernel
#print axioms leaf01328_w_row032_weighted
#print axioms leaf01328_w_row032_identity
#print axioms leaf01328_w_row032_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
