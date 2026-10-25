/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_weights20 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 33 1 32000 60 leaf00005_w_segment20)
theorem leaf00005_w_weights20_identity : leaf00005_w_weights20=IntegerWeightedOuter.weights 33 1 32000 60 leaf00005_w_segment20 := by decide +kernel
noncomputable def leaf00005_w_piece20 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00005_w_weights20 leaf00005_w_segment20)
theorem leaf00005_w_piece20_weighted : leaf00005_w_piece20=IntegerWeightedOuter.applyWeights leaf00005_w_weights20 leaf00005_w_segment20 := by decide +kernel
theorem leaf00005_w_piece20_identity : leaf00005_w_piece20=IntegerOuterTerms.transform 33 1 32000 60 leaf00005_w_segment20 :=
  IntegerWeightedOuter.checked 33 1 32000 60 leaf00005_w_segment20 leaf00005_w_piece20 leaf00005_w_weights20 leaf00005_w_weights20_identity leaf00005_w_piece20_weighted
#print axioms leaf00005_w_weights20_identity
#print axioms leaf00005_w_piece20_weighted
#print axioms leaf00005_w_piece20_identity
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
