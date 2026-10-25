/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_weights04 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 4 1 4096 12 leaf03800_w_segment04)
theorem leaf03800_w_weights04_identity : leaf03800_w_weights04=IntegerWeightedOuter.weights 4 1 4096 12 leaf03800_w_segment04 := by decide +kernel
noncomputable def leaf03800_w_piece04 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf03800_w_weights04 leaf03800_w_segment04)
theorem leaf03800_w_piece04_weighted : leaf03800_w_piece04=IntegerWeightedOuter.applyWeights leaf03800_w_weights04 leaf03800_w_segment04 := by decide +kernel
theorem leaf03800_w_piece04_identity : leaf03800_w_piece04=IntegerOuterTerms.transform 4 1 4096 12 leaf03800_w_segment04 :=
  IntegerWeightedOuter.checked 4 1 4096 12 leaf03800_w_segment04 leaf03800_w_piece04 leaf03800_w_weights04 leaf03800_w_weights04_identity leaf03800_w_piece04_weighted
#print axioms leaf03800_w_weights04_identity
#print axioms leaf03800_w_piece04_weighted
#print axioms leaf03800_w_piece04_identity
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
