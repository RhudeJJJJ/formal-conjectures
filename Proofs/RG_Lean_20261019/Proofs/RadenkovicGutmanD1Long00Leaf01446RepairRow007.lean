/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01446RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01446_w_row007 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row007 leaf01446_w_affine)
theorem leaf01446_w_row007_weighted : leaf01446_w_row007=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row007 leaf01446_w_affine := by decide +kernel
theorem leaf01446_w_row007_identity : leaf01446_w_row007=NestedInteger.coefficientFrom 88 7 0 leaf01446_w_affine :=
  IntegerWeightedBernstein.checked 88 7 0 leaf01446_w_affine leaf01446_w_row007 IntegerBernsteinWeights88.row007 (IntegerBernsteinTable.checked (n := 2) 88 7 0 89 leaf01446_w_affine IntegerBernsteinWeights88.row007 leaf01446_w_affine_length IntegerBernsteinWeights88.row007_identity) leaf01446_w_row007_weighted
theorem leaf01446_w_row007_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01446_w_row007=true := by decide +kernel
#print axioms leaf01446_w_row007_weighted
#print axioms leaf01446_w_row007_identity
#print axioms leaf01446_w_row007_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
