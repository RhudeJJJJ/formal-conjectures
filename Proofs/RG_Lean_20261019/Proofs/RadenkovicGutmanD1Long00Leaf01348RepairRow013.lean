/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01348RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01348_w_row013 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row013 leaf01348_w_affine)
theorem leaf01348_w_row013_weighted : leaf01348_w_row013=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row013 leaf01348_w_affine := by decide +kernel
theorem leaf01348_w_row013_identity : leaf01348_w_row013=NestedInteger.coefficientFrom 88 13 0 leaf01348_w_affine :=
  IntegerWeightedBernstein.checked 88 13 0 leaf01348_w_affine leaf01348_w_row013 IntegerBernsteinWeights88.row013 (IntegerBernsteinTable.checked (n := 2) 88 13 0 89 leaf01348_w_affine IntegerBernsteinWeights88.row013 leaf01348_w_affine_length IntegerBernsteinWeights88.row013_identity) leaf01348_w_row013_weighted
theorem leaf01348_w_row013_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01348_w_row013=true := by decide +kernel
#print axioms leaf01348_w_row013_weighted
#print axioms leaf01348_w_row013_identity
#print axioms leaf01348_w_row013_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
