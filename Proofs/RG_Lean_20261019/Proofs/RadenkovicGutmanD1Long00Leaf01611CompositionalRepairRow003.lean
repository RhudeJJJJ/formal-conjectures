/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01611CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01611_w_row003 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row003 leaf01611_w_affine)
theorem leaf01611_w_row003_weighted : leaf01611_w_row003=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row003 leaf01611_w_affine := by decide +kernel
theorem leaf01611_w_row003_identity : leaf01611_w_row003=NestedInteger.coefficientFrom 88 3 0 leaf01611_w_affine :=
  IntegerWeightedBernstein.checked 88 3 0 leaf01611_w_affine leaf01611_w_row003 IntegerBernsteinWeights88.row003 (IntegerBernsteinTable.checked (n := 2) 88 3 0 89 leaf01611_w_affine IntegerBernsteinWeights88.row003 leaf01611_w_affine_length IntegerBernsteinWeights88.row003_identity) leaf01611_w_row003_weighted
theorem leaf01611_w_row003_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01611_w_row003=true := by decide +kernel
#print axioms leaf01611_w_row003_weighted
#print axioms leaf01611_w_row003_identity
#print axioms leaf01611_w_row003_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
