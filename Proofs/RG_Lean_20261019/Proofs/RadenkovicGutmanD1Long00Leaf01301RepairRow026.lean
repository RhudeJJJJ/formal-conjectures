/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01301RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01301_w_row026 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf01301_w_affine)
theorem leaf01301_w_row026_weighted : leaf01301_w_row026=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row026 leaf01301_w_affine := by decide +kernel
theorem leaf01301_w_row026_identity : leaf01301_w_row026=NestedInteger.coefficientFrom 88 26 0 leaf01301_w_affine :=
  IntegerWeightedBernstein.checked 88 26 0 leaf01301_w_affine leaf01301_w_row026 IntegerBernsteinWeights88.row026 (IntegerBernsteinTable.checked (n := 2) 88 26 0 89 leaf01301_w_affine IntegerBernsteinWeights88.row026 leaf01301_w_affine_length IntegerBernsteinWeights88.row026_identity) leaf01301_w_row026_weighted
theorem leaf01301_w_row026_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01301_w_row026=true := by decide +kernel
#print axioms leaf01301_w_row026_weighted
#print axioms leaf01301_w_row026_identity
#print axioms leaf01301_w_row026_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
