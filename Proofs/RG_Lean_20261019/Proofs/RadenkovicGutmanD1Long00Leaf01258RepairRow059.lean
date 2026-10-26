/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01258RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01258_w_row059 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row059 leaf01258_w_affine)
theorem leaf01258_w_row059_weighted : leaf01258_w_row059=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row059 leaf01258_w_affine := by decide +kernel
theorem leaf01258_w_row059_identity : leaf01258_w_row059=NestedInteger.coefficientFrom 88 59 0 leaf01258_w_affine :=
  IntegerWeightedBernstein.checked 88 59 0 leaf01258_w_affine leaf01258_w_row059 IntegerBernsteinWeights88.row059 (IntegerBernsteinTable.checked (n := 2) 88 59 0 89 leaf01258_w_affine IntegerBernsteinWeights88.row059 leaf01258_w_affine_length IntegerBernsteinWeights88.row059_identity) leaf01258_w_row059_weighted
theorem leaf01258_w_row059_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01258_w_row059=true := by decide +kernel
#print axioms leaf01258_w_row059_weighted
#print axioms leaf01258_w_row059_identity
#print axioms leaf01258_w_row059_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
