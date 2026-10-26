/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01607CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01607_w_row008 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row008 leaf01607_w_affine)
theorem leaf01607_w_row008_weighted : leaf01607_w_row008=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row008 leaf01607_w_affine := by decide +kernel
theorem leaf01607_w_row008_identity : leaf01607_w_row008=NestedInteger.coefficientFrom 88 8 0 leaf01607_w_affine :=
  IntegerWeightedBernstein.checked 88 8 0 leaf01607_w_affine leaf01607_w_row008 IntegerBernsteinWeights88.row008 (IntegerBernsteinTable.checked (n := 2) 88 8 0 89 leaf01607_w_affine IntegerBernsteinWeights88.row008 leaf01607_w_affine_length IntegerBernsteinWeights88.row008_identity) leaf01607_w_row008_weighted
theorem leaf01607_w_row008_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01607_w_row008=true := by decide +kernel
#print axioms leaf01607_w_row008_weighted
#print axioms leaf01607_w_row008_identity
#print axioms leaf01607_w_row008_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
