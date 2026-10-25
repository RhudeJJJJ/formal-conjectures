/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01334RepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01334_w_row043 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row043 leaf01334_w_affine)
theorem leaf01334_w_row043_weighted : leaf01334_w_row043=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row043 leaf01334_w_affine := by decide +kernel
theorem leaf01334_w_row043_identity : leaf01334_w_row043=NestedInteger.coefficientFrom 88 43 0 leaf01334_w_affine :=
  IntegerWeightedBernstein.checked 88 43 0 leaf01334_w_affine leaf01334_w_row043 IntegerBernsteinWeights88.row043 (IntegerBernsteinTable.checked (n := 2) 88 43 0 89 leaf01334_w_affine IntegerBernsteinWeights88.row043 leaf01334_w_affine_length IntegerBernsteinWeights88.row043_identity) leaf01334_w_row043_weighted
theorem leaf01334_w_row043_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01334_w_row043=true := by decide +kernel
#print axioms leaf01334_w_row043_weighted
#print axioms leaf01334_w_row043_identity
#print axioms leaf01334_w_row043_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
