/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01329RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01329_w_row053 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row053 leaf01329_w_affine)
theorem leaf01329_w_row053_weighted : leaf01329_w_row053=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row053 leaf01329_w_affine := by decide +kernel
theorem leaf01329_w_row053_identity : leaf01329_w_row053=NestedInteger.coefficientFrom 88 53 0 leaf01329_w_affine :=
  IntegerWeightedBernstein.checked 88 53 0 leaf01329_w_affine leaf01329_w_row053 IntegerBernsteinWeights88.row053 (IntegerBernsteinTable.checked (n := 2) 88 53 0 89 leaf01329_w_affine IntegerBernsteinWeights88.row053 leaf01329_w_affine_length IntegerBernsteinWeights88.row053_identity) leaf01329_w_row053_weighted
theorem leaf01329_w_row053_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01329_w_row053=true := by decide +kernel
#print axioms leaf01329_w_row053_weighted
#print axioms leaf01329_w_row053_identity
#print axioms leaf01329_w_row053_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
