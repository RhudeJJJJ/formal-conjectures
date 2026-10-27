/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01346RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01346_w_row076 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row076 leaf01346_w_affine)
theorem leaf01346_w_row076_weighted : leaf01346_w_row076=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row076 leaf01346_w_affine := by decide +kernel
theorem leaf01346_w_row076_identity : leaf01346_w_row076=NestedInteger.coefficientFrom 88 76 0 leaf01346_w_affine :=
  IntegerWeightedBernstein.checked 88 76 0 leaf01346_w_affine leaf01346_w_row076 IntegerBernsteinWeights88.row076 (IntegerBernsteinTable.checked (n := 2) 88 76 0 89 leaf01346_w_affine IntegerBernsteinWeights88.row076 leaf01346_w_affine_length IntegerBernsteinWeights88.row076_identity) leaf01346_w_row076_weighted
theorem leaf01346_w_row076_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01346_w_row076=true := by decide +kernel
#print axioms leaf01346_w_row076_weighted
#print axioms leaf01346_w_row076_identity
#print axioms leaf01346_w_row076_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
