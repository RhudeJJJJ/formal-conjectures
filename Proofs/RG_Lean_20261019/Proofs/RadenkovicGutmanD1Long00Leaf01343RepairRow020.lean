/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01343RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01343_w_row020 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row020 leaf01343_w_affine)
theorem leaf01343_w_row020_weighted : leaf01343_w_row020=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row020 leaf01343_w_affine := by decide +kernel
theorem leaf01343_w_row020_identity : leaf01343_w_row020=NestedInteger.coefficientFrom 88 20 0 leaf01343_w_affine :=
  IntegerWeightedBernstein.checked 88 20 0 leaf01343_w_affine leaf01343_w_row020 IntegerBernsteinWeights88.row020 (IntegerBernsteinTable.checked (n := 2) 88 20 0 89 leaf01343_w_affine IntegerBernsteinWeights88.row020 leaf01343_w_affine_length IntegerBernsteinWeights88.row020_identity) leaf01343_w_row020_weighted
theorem leaf01343_w_row020_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01343_w_row020=true := by decide +kernel
#print axioms leaf01343_w_row020_weighted
#print axioms leaf01343_w_row020_identity
#print axioms leaf01343_w_row020_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
