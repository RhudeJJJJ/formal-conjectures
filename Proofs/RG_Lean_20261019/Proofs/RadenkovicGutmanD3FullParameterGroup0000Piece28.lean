/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0000Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_weights28 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 32 1 32000 84 leaf00000_w_segment28)
theorem leaf00000_w_weights28_identity : leaf00000_w_weights28=IntegerWeightedOuter.weights 32 1 32000 84 leaf00000_w_segment28 := by decide +kernel
noncomputable def leaf00000_w_piece28 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00000_w_weights28 leaf00000_w_segment28)
theorem leaf00000_w_piece28_weighted : leaf00000_w_piece28=IntegerWeightedOuter.applyWeights leaf00000_w_weights28 leaf00000_w_segment28 := by decide +kernel
theorem leaf00000_w_piece28_identity : leaf00000_w_piece28=IntegerOuterTerms.transform 32 1 32000 84 leaf00000_w_segment28 :=
  IntegerWeightedOuter.checked 32 1 32000 84 leaf00000_w_segment28 leaf00000_w_piece28 leaf00000_w_weights28 leaf00000_w_weights28_identity leaf00000_w_piece28_weighted
#print axioms leaf00000_w_weights28_identity
#print axioms leaf00000_w_piece28_weighted
#print axioms leaf00000_w_piece28_identity
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
