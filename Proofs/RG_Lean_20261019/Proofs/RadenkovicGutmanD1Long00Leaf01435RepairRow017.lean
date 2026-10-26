/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01435RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01435_w_row017 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf01435_w_affine)
theorem leaf01435_w_row017_weighted : leaf01435_w_row017=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row017 leaf01435_w_affine := by decide +kernel
theorem leaf01435_w_row017_identity : leaf01435_w_row017=NestedInteger.coefficientFrom 88 17 0 leaf01435_w_affine :=
  IntegerWeightedBernstein.checked 88 17 0 leaf01435_w_affine leaf01435_w_row017 IntegerBernsteinWeights88.row017 (IntegerBernsteinTable.checked (n := 2) 88 17 0 89 leaf01435_w_affine IntegerBernsteinWeights88.row017 leaf01435_w_affine_length IntegerBernsteinWeights88.row017_identity) leaf01435_w_row017_weighted
theorem leaf01435_w_row017_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01435_w_row017=true := by decide +kernel
#print axioms leaf01435_w_row017_weighted
#print axioms leaf01435_w_row017_identity
#print axioms leaf01435_w_row017_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
