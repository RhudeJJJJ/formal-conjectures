/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01505RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01505_w_row050 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row050 leaf01505_w_affine)
theorem leaf01505_w_row050_weighted : leaf01505_w_row050=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row050 leaf01505_w_affine := by decide +kernel
theorem leaf01505_w_row050_identity : leaf01505_w_row050=NestedInteger.coefficientFrom 88 50 0 leaf01505_w_affine :=
  IntegerWeightedBernstein.checked 88 50 0 leaf01505_w_affine leaf01505_w_row050 IntegerBernsteinWeights88.row050 (IntegerBernsteinTable.checked (n := 2) 88 50 0 89 leaf01505_w_affine IntegerBernsteinWeights88.row050 leaf01505_w_affine_length IntegerBernsteinWeights88.row050_identity) leaf01505_w_row050_weighted
theorem leaf01505_w_row050_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01505_w_row050=true := by decide +kernel
#print axioms leaf01505_w_row050_weighted
#print axioms leaf01505_w_row050_identity
#print axioms leaf01505_w_row050_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
