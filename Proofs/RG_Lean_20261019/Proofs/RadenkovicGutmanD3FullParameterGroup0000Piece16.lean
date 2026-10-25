/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0000Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_weights16 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 32 1 32000 48 leaf00000_w_segment16)
theorem leaf00000_w_weights16_identity : leaf00000_w_weights16=IntegerWeightedOuter.weights 32 1 32000 48 leaf00000_w_segment16 := by decide +kernel
noncomputable def leaf00000_w_piece16 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00000_w_weights16 leaf00000_w_segment16)
theorem leaf00000_w_piece16_weighted : leaf00000_w_piece16=IntegerWeightedOuter.applyWeights leaf00000_w_weights16 leaf00000_w_segment16 := by decide +kernel
theorem leaf00000_w_piece16_identity : leaf00000_w_piece16=IntegerOuterTerms.transform 32 1 32000 48 leaf00000_w_segment16 :=
  IntegerWeightedOuter.checked 32 1 32000 48 leaf00000_w_segment16 leaf00000_w_piece16 leaf00000_w_weights16 leaf00000_w_weights16_identity leaf00000_w_piece16_weighted
#print axioms leaf00000_w_weights16_identity
#print axioms leaf00000_w_piece16_weighted
#print axioms leaf00000_w_piece16_identity
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
