/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01339RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01339_w_row024 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01339_w_affine)
theorem leaf01339_w_row024_weighted : leaf01339_w_row024=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row024 leaf01339_w_affine := by decide +kernel
theorem leaf01339_w_row024_identity : leaf01339_w_row024=NestedInteger.coefficientFrom 88 24 0 leaf01339_w_affine :=
  IntegerWeightedBernstein.checked 88 24 0 leaf01339_w_affine leaf01339_w_row024 IntegerBernsteinWeights88.row024 (IntegerBernsteinTable.checked (n := 2) 88 24 0 89 leaf01339_w_affine IntegerBernsteinWeights88.row024 leaf01339_w_affine_length IntegerBernsteinWeights88.row024_identity) leaf01339_w_row024_weighted
theorem leaf01339_w_row024_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01339_w_row024=true := by decide +kernel
#print axioms leaf01339_w_row024_weighted
#print axioms leaf01339_w_row024_identity
#print axioms leaf01339_w_row024_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
