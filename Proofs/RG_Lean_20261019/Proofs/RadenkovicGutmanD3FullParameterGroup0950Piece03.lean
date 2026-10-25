/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_weights03 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 4 1 4096 9 leaf03800_w_segment03)
theorem leaf03800_w_weights03_identity : leaf03800_w_weights03=IntegerWeightedOuter.weights 4 1 4096 9 leaf03800_w_segment03 := by decide +kernel
noncomputable def leaf03800_w_piece03 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf03800_w_weights03 leaf03800_w_segment03)
theorem leaf03800_w_piece03_weighted : leaf03800_w_piece03=IntegerWeightedOuter.applyWeights leaf03800_w_weights03 leaf03800_w_segment03 := by decide +kernel
theorem leaf03800_w_piece03_identity : leaf03800_w_piece03=IntegerOuterTerms.transform 4 1 4096 9 leaf03800_w_segment03 :=
  IntegerWeightedOuter.checked 4 1 4096 9 leaf03800_w_segment03 leaf03800_w_piece03 leaf03800_w_weights03 leaf03800_w_weights03_identity leaf03800_w_piece03_weighted
#print axioms leaf03800_w_weights03_identity
#print axioms leaf03800_w_piece03_weighted
#print axioms leaf03800_w_piece03_identity
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
