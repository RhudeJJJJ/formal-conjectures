/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01300RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01300_w_row075 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row075 leaf01300_w_affine)
theorem leaf01300_w_row075_weighted : leaf01300_w_row075=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row075 leaf01300_w_affine := by decide +kernel
theorem leaf01300_w_row075_identity : leaf01300_w_row075=NestedInteger.coefficientFrom 88 75 0 leaf01300_w_affine :=
  IntegerWeightedBernstein.checked 88 75 0 leaf01300_w_affine leaf01300_w_row075 IntegerBernsteinWeights88.row075 (IntegerBernsteinTable.checked (n := 2) 88 75 0 89 leaf01300_w_affine IntegerBernsteinWeights88.row075 leaf01300_w_affine_length IntegerBernsteinWeights88.row075_identity) leaf01300_w_row075_weighted
theorem leaf01300_w_row075_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01300_w_row075=true := by decide +kernel
#print axioms leaf01300_w_row075_weighted
#print axioms leaf01300_w_row075_identity
#print axioms leaf01300_w_row075_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
