/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01612CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01612_w_row065 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row065 leaf01612_w_affine)
theorem leaf01612_w_row065_weighted : leaf01612_w_row065=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row065 leaf01612_w_affine := by decide +kernel
theorem leaf01612_w_row065_identity : leaf01612_w_row065=NestedInteger.coefficientFrom 88 65 0 leaf01612_w_affine :=
  IntegerWeightedBernstein.checked 88 65 0 leaf01612_w_affine leaf01612_w_row065 IntegerBernsteinWeights88.row065 (IntegerBernsteinTable.checked (n := 2) 88 65 0 89 leaf01612_w_affine IntegerBernsteinWeights88.row065 leaf01612_w_affine_length IntegerBernsteinWeights88.row065_identity) leaf01612_w_row065_weighted
theorem leaf01612_w_row065_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01612_w_row065=true := by decide +kernel
#print axioms leaf01612_w_row065_weighted
#print axioms leaf01612_w_row065_identity
#print axioms leaf01612_w_row065_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
