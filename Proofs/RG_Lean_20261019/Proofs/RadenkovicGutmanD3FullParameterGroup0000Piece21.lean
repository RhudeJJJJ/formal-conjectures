/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0000Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_weights21 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 32 1 32000 63 leaf00000_w_segment21)
theorem leaf00000_w_weights21_identity : leaf00000_w_weights21=IntegerWeightedOuter.weights 32 1 32000 63 leaf00000_w_segment21 := by decide +kernel
noncomputable def leaf00000_w_piece21 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00000_w_weights21 leaf00000_w_segment21)
theorem leaf00000_w_piece21_weighted : leaf00000_w_piece21=IntegerWeightedOuter.applyWeights leaf00000_w_weights21 leaf00000_w_segment21 := by decide +kernel
theorem leaf00000_w_piece21_identity : leaf00000_w_piece21=IntegerOuterTerms.transform 32 1 32000 63 leaf00000_w_segment21 :=
  IntegerWeightedOuter.checked 32 1 32000 63 leaf00000_w_segment21 leaf00000_w_piece21 leaf00000_w_weights21 leaf00000_w_weights21_identity leaf00000_w_piece21_weighted
#print axioms leaf00000_w_weights21_identity
#print axioms leaf00000_w_piece21_weighted
#print axioms leaf00000_w_piece21_identity
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
