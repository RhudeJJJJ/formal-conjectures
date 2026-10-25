/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01339RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01339_w_row045 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row045 leaf01339_w_affine)
theorem leaf01339_w_row045_weighted : leaf01339_w_row045=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row045 leaf01339_w_affine := by decide +kernel
theorem leaf01339_w_row045_identity : leaf01339_w_row045=NestedInteger.coefficientFrom 88 45 0 leaf01339_w_affine :=
  IntegerWeightedBernstein.checked 88 45 0 leaf01339_w_affine leaf01339_w_row045 IntegerBernsteinWeights88.row045 (IntegerBernsteinTable.checked (n := 2) 88 45 0 89 leaf01339_w_affine IntegerBernsteinWeights88.row045 leaf01339_w_affine_length IntegerBernsteinWeights88.row045_identity) leaf01339_w_row045_weighted
theorem leaf01339_w_row045_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01339_w_row045=true := by decide +kernel
#print axioms leaf01339_w_row045_weighted
#print axioms leaf01339_w_row045_identity
#print axioms leaf01339_w_row045_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
