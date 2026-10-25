/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0950Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf03800_w_weights21 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 4 1 4096 63 leaf03800_w_segment21)
theorem leaf03800_w_weights21_identity : leaf03800_w_weights21=IntegerWeightedOuter.weights 4 1 4096 63 leaf03800_w_segment21 := by decide +kernel
noncomputable def leaf03800_w_piece21 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf03800_w_weights21 leaf03800_w_segment21)
theorem leaf03800_w_piece21_weighted : leaf03800_w_piece21=IntegerWeightedOuter.applyWeights leaf03800_w_weights21 leaf03800_w_segment21 := by decide +kernel
theorem leaf03800_w_piece21_identity : leaf03800_w_piece21=IntegerOuterTerms.transform 4 1 4096 63 leaf03800_w_segment21 :=
  IntegerWeightedOuter.checked 4 1 4096 63 leaf03800_w_segment21 leaf03800_w_piece21 leaf03800_w_weights21 leaf03800_w_weights21_identity leaf03800_w_piece21_weighted
#print axioms leaf03800_w_weights21_identity
#print axioms leaf03800_w_piece21_weighted
#print axioms leaf03800_w_piece21_identity
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0950
