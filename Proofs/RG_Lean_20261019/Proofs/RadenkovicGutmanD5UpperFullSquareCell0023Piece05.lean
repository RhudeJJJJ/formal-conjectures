/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5UpperFullSquareCell0023Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00023_w_weights05 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 27 1 3200 15 leaf00023_w_segment05)
theorem leaf00023_w_weights05_identity : leaf00023_w_weights05=IntegerWeightedOuter.weights 27 1 3200 15 leaf00023_w_segment05 := by decide +kernel
noncomputable def leaf00023_w_piece05 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00023_w_weights05 leaf00023_w_segment05)
theorem leaf00023_w_piece05_weighted : leaf00023_w_piece05=IntegerWeightedOuter.applyWeights leaf00023_w_weights05 leaf00023_w_segment05 := by decide +kernel
theorem leaf00023_w_piece05_identity : leaf00023_w_piece05=IntegerOuterTerms.transform 27 1 3200 15 leaf00023_w_segment05 :=
  IntegerWeightedOuter.checked 27 1 3200 15 leaf00023_w_segment05 leaf00023_w_piece05 leaf00023_w_weights05 leaf00023_w_weights05_identity leaf00023_w_piece05_weighted
#print axioms leaf00023_w_weights05_identity
#print axioms leaf00023_w_piece05_weighted
#print axioms leaf00023_w_piece05_identity
end Gebendorfer.RadenkovicGutman.D5UpperFullSquareCell0023
