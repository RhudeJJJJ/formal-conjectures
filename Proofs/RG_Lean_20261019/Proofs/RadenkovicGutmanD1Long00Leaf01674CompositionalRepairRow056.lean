/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01674CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01674_w_row056 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row056 leaf01674_w_affine)
theorem leaf01674_w_row056_weighted : leaf01674_w_row056=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row056 leaf01674_w_affine := by decide +kernel
theorem leaf01674_w_row056_identity : leaf01674_w_row056=NestedInteger.coefficientFrom 88 56 0 leaf01674_w_affine :=
  IntegerWeightedBernstein.checked 88 56 0 leaf01674_w_affine leaf01674_w_row056 IntegerBernsteinWeights88.row056 (IntegerBernsteinTable.checked (n := 2) 88 56 0 89 leaf01674_w_affine IntegerBernsteinWeights88.row056 leaf01674_w_affine_length IntegerBernsteinWeights88.row056_identity) leaf01674_w_row056_weighted
theorem leaf01674_w_row056_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01674_w_row056=true := by decide +kernel
#print axioms leaf01674_w_row056_weighted
#print axioms leaf01674_w_row056_identity
#print axioms leaf01674_w_row056_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
