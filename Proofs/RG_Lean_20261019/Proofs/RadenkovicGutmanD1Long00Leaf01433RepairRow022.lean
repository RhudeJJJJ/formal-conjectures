/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01433RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01433_w_row022 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row022 leaf01433_w_affine)
theorem leaf01433_w_row022_weighted : leaf01433_w_row022=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row022 leaf01433_w_affine := by decide +kernel
theorem leaf01433_w_row022_identity : leaf01433_w_row022=NestedInteger.coefficientFrom 88 22 0 leaf01433_w_affine :=
  IntegerWeightedBernstein.checked 88 22 0 leaf01433_w_affine leaf01433_w_row022 IntegerBernsteinWeights88.row022 (IntegerBernsteinTable.checked (n := 2) 88 22 0 89 leaf01433_w_affine IntegerBernsteinWeights88.row022 leaf01433_w_affine_length IntegerBernsteinWeights88.row022_identity) leaf01433_w_row022_weighted
theorem leaf01433_w_row022_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01433_w_row022=true := by decide +kernel
#print axioms leaf01433_w_row022_weighted
#print axioms leaf01433_w_row022_identity
#print axioms leaf01433_w_row022_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
