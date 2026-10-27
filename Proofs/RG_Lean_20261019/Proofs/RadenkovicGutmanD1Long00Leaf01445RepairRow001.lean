/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01445RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01445_w_row001 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row001 leaf01445_w_affine)
theorem leaf01445_w_row001_weighted : leaf01445_w_row001=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row001 leaf01445_w_affine := by decide +kernel
theorem leaf01445_w_row001_identity : leaf01445_w_row001=NestedInteger.coefficientFrom 88 1 0 leaf01445_w_affine :=
  IntegerWeightedBernstein.checked 88 1 0 leaf01445_w_affine leaf01445_w_row001 IntegerBernsteinWeights88.row001 (IntegerBernsteinTable.checked (n := 2) 88 1 0 89 leaf01445_w_affine IntegerBernsteinWeights88.row001 leaf01445_w_affine_length IntegerBernsteinWeights88.row001_identity) leaf01445_w_row001_weighted
theorem leaf01445_w_row001_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01445_w_row001=true := by decide +kernel
#print axioms leaf01445_w_row001_weighted
#print axioms leaf01445_w_row001_identity
#print axioms leaf01445_w_row001_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
