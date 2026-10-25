/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_weights12 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 559 3 12800 36 leaf01900_w_segment12)
theorem leaf01900_w_weights12_identity : leaf01900_w_weights12=IntegerWeightedOuter.weights 559 3 12800 36 leaf01900_w_segment12 := by decide +kernel
noncomputable def leaf01900_w_piece12 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01900_w_weights12 leaf01900_w_segment12)
theorem leaf01900_w_piece12_weighted : leaf01900_w_piece12=IntegerWeightedOuter.applyWeights leaf01900_w_weights12 leaf01900_w_segment12 := by decide +kernel
theorem leaf01900_w_piece12_identity : leaf01900_w_piece12=IntegerOuterTerms.transform 559 3 12800 36 leaf01900_w_segment12 :=
  IntegerWeightedOuter.checked 559 3 12800 36 leaf01900_w_segment12 leaf01900_w_piece12 leaf01900_w_weights12 leaf01900_w_weights12_identity leaf01900_w_piece12_weighted
#print axioms leaf01900_w_weights12_identity
#print axioms leaf01900_w_piece12_weighted
#print axioms leaf01900_w_piece12_identity
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
