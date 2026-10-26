/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01604CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01604_w_row009 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row009 leaf01604_w_affine)
theorem leaf01604_w_row009_weighted : leaf01604_w_row009=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row009 leaf01604_w_affine := by decide +kernel
theorem leaf01604_w_row009_identity : leaf01604_w_row009=NestedInteger.coefficientFrom 88 9 0 leaf01604_w_affine :=
  IntegerWeightedBernstein.checked 88 9 0 leaf01604_w_affine leaf01604_w_row009 IntegerBernsteinWeights88.row009 (IntegerBernsteinTable.checked (n := 2) 88 9 0 89 leaf01604_w_affine IntegerBernsteinWeights88.row009 leaf01604_w_affine_length IntegerBernsteinWeights88.row009_identity) leaf01604_w_row009_weighted
theorem leaf01604_w_row009_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01604_w_row009=true := by decide +kernel
#print axioms leaf01604_w_row009_weighted
#print axioms leaf01604_w_row009_identity
#print axioms leaf01604_w_row009_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
