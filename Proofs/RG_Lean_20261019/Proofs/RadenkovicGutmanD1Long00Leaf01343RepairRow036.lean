/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01343RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01343_w_row036 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row036 leaf01343_w_affine)
theorem leaf01343_w_row036_weighted : leaf01343_w_row036=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row036 leaf01343_w_affine := by decide +kernel
theorem leaf01343_w_row036_identity : leaf01343_w_row036=NestedInteger.coefficientFrom 88 36 0 leaf01343_w_affine :=
  IntegerWeightedBernstein.checked 88 36 0 leaf01343_w_affine leaf01343_w_row036 IntegerBernsteinWeights88.row036 (IntegerBernsteinTable.checked (n := 2) 88 36 0 89 leaf01343_w_affine IntegerBernsteinWeights88.row036 leaf01343_w_affine_length IntegerBernsteinWeights88.row036_identity) leaf01343_w_row036_weighted
theorem leaf01343_w_row036_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01343_w_row036=true := by decide +kernel
#print axioms leaf01343_w_row036_weighted
#print axioms leaf01343_w_row036_identity
#print axioms leaf01343_w_row036_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
