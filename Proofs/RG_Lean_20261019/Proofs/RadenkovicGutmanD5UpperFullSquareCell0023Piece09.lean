/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_weights09 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 27 1 3200 27 leaf00023_w_segment09)
theorem leaf00023_w_weights09_identity : leaf00023_w_weights09=IntegerWeightedOuter.weights 27 1 3200 27 leaf00023_w_segment09 := by decide +kernel
noncomputable def leaf00023_w_piece09 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00023_w_weights09 leaf00023_w_segment09)
theorem leaf00023_w_piece09_weighted : leaf00023_w_piece09=IntegerWeightedOuter.applyWeights leaf00023_w_weights09 leaf00023_w_segment09 := by decide +kernel
theorem leaf00023_w_piece09_identity : leaf00023_w_piece09=IntegerOuterTerms.transform 27 1 3200 27 leaf00023_w_segment09 :=
  IntegerWeightedOuter.checked 27 1 3200 27 leaf00023_w_segment09 leaf00023_w_piece09 leaf00023_w_weights09 leaf00023_w_weights09_identity leaf00023_w_piece09_weighted
#print axioms leaf00023_w_weights09_identity
#print axioms leaf00023_w_piece09_weighted
#print axioms leaf00023_w_piece09_identity
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
