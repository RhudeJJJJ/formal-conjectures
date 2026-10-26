/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01297RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01297_w_row062 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row062 leaf01297_w_affine)
theorem leaf01297_w_row062_weighted : leaf01297_w_row062=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row062 leaf01297_w_affine := by decide +kernel
theorem leaf01297_w_row062_identity : leaf01297_w_row062=NestedInteger.coefficientFrom 88 62 0 leaf01297_w_affine :=
  IntegerWeightedBernstein.checked 88 62 0 leaf01297_w_affine leaf01297_w_row062 IntegerBernsteinWeights88.row062 (IntegerBernsteinTable.checked (n := 2) 88 62 0 89 leaf01297_w_affine IntegerBernsteinWeights88.row062 leaf01297_w_affine_length IntegerBernsteinWeights88.row062_identity) leaf01297_w_row062_weighted
theorem leaf01297_w_row062_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01297_w_row062=true := by decide +kernel
#print axioms leaf01297_w_row062_weighted
#print axioms leaf01297_w_row062_identity
#print axioms leaf01297_w_row062_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
