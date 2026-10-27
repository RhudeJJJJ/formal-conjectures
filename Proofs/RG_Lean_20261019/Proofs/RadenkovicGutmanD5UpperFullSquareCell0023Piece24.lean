/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_weights24 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 27 1 3200 72 leaf00023_w_segment24)
theorem leaf00023_w_weights24_identity : leaf00023_w_weights24=IntegerWeightedOuter.weights 27 1 3200 72 leaf00023_w_segment24 := by decide +kernel
noncomputable def leaf00023_w_piece24 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00023_w_weights24 leaf00023_w_segment24)
theorem leaf00023_w_piece24_weighted : leaf00023_w_piece24=IntegerWeightedOuter.applyWeights leaf00023_w_weights24 leaf00023_w_segment24 := by decide +kernel
theorem leaf00023_w_piece24_identity : leaf00023_w_piece24=IntegerOuterTerms.transform 27 1 3200 72 leaf00023_w_segment24 :=
  IntegerWeightedOuter.checked 27 1 3200 72 leaf00023_w_segment24 leaf00023_w_piece24 leaf00023_w_weights24 leaf00023_w_weights24_identity leaf00023_w_piece24_weighted
#print axioms leaf00023_w_weights24_identity
#print axioms leaf00023_w_piece24_weighted
#print axioms leaf00023_w_piece24_identity
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
