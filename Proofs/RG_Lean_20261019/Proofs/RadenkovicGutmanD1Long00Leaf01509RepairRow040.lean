/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01509RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01509_w_row040 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row040 leaf01509_w_affine)
theorem leaf01509_w_row040_weighted : leaf01509_w_row040=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row040 leaf01509_w_affine := by decide +kernel
theorem leaf01509_w_row040_identity : leaf01509_w_row040=NestedInteger.coefficientFrom 88 40 0 leaf01509_w_affine :=
  IntegerWeightedBernstein.checked 88 40 0 leaf01509_w_affine leaf01509_w_row040 IntegerBernsteinWeights88.row040 (IntegerBernsteinTable.checked (n := 2) 88 40 0 89 leaf01509_w_affine IntegerBernsteinWeights88.row040 leaf01509_w_affine_length IntegerBernsteinWeights88.row040_identity) leaf01509_w_row040_weighted
theorem leaf01509_w_row040_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01509_w_row040=true := by decide +kernel
#print axioms leaf01509_w_row040_weighted
#print axioms leaf01509_w_row040_identity
#print axioms leaf01509_w_row040_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
