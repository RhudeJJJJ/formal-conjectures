/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_weights10 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 33 1 32000 30 leaf00005_w_segment10)
theorem leaf00005_w_weights10_identity : leaf00005_w_weights10=IntegerWeightedOuter.weights 33 1 32000 30 leaf00005_w_segment10 := by decide +kernel
noncomputable def leaf00005_w_piece10 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00005_w_weights10 leaf00005_w_segment10)
theorem leaf00005_w_piece10_weighted : leaf00005_w_piece10=IntegerWeightedOuter.applyWeights leaf00005_w_weights10 leaf00005_w_segment10 := by decide +kernel
theorem leaf00005_w_piece10_identity : leaf00005_w_piece10=IntegerOuterTerms.transform 33 1 32000 30 leaf00005_w_segment10 :=
  IntegerWeightedOuter.checked 33 1 32000 30 leaf00005_w_segment10 leaf00005_w_piece10 leaf00005_w_weights10 leaf00005_w_weights10_identity leaf00005_w_piece10_weighted
#print axioms leaf00005_w_weights10_identity
#print axioms leaf00005_w_piece10_weighted
#print axioms leaf00005_w_piece10_identity
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
