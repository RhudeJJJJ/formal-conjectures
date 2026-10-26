/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01264RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01264_w_row047 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row047 leaf01264_w_affine)
theorem leaf01264_w_row047_weighted : leaf01264_w_row047=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row047 leaf01264_w_affine := by decide +kernel
theorem leaf01264_w_row047_identity : leaf01264_w_row047=NestedInteger.coefficientFrom 88 47 0 leaf01264_w_affine :=
  IntegerWeightedBernstein.checked 88 47 0 leaf01264_w_affine leaf01264_w_row047 IntegerBernsteinWeights88.row047 (IntegerBernsteinTable.checked (n := 2) 88 47 0 89 leaf01264_w_affine IntegerBernsteinWeights88.row047 leaf01264_w_affine_length IntegerBernsteinWeights88.row047_identity) leaf01264_w_row047_weighted
theorem leaf01264_w_row047_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01264_w_row047=true := by decide +kernel
#print axioms leaf01264_w_row047_weighted
#print axioms leaf01264_w_row047_identity
#print axioms leaf01264_w_row047_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
