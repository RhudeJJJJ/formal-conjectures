/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01609CompositionalRepairAffineLength
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01609_w_row064 : NestedInteger.Poly 2 := rg_closed_integer_row% (IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row064 leaf01609_w_affine)
theorem leaf01609_w_row064_weighted : leaf01609_w_row064=IntegerWeightedBernstein.applyWeights IntegerBernsteinWeights88.row064 leaf01609_w_affine := by decide +kernel
theorem leaf01609_w_row064_identity : leaf01609_w_row064=NestedInteger.coefficientFrom 88 64 0 leaf01609_w_affine :=
  IntegerWeightedBernstein.checked 88 64 0 leaf01609_w_affine leaf01609_w_row064 IntegerBernsteinWeights88.row064 (IntegerBernsteinTable.checked (n := 2) 88 64 0 89 leaf01609_w_affine IntegerBernsteinWeights88.row064 leaf01609_w_affine_length IntegerBernsteinWeights88.row064_identity) leaf01609_w_row064_weighted
theorem leaf01609_w_row064_positive : NestedInteger.bernsteinCheck 2 ![4,4] leaf01609_w_row064=true := by decide +kernel
#print axioms leaf01609_w_row064_weighted
#print axioms leaf01609_w_row064_identity
#print axioms leaf01609_w_row064_positive
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
