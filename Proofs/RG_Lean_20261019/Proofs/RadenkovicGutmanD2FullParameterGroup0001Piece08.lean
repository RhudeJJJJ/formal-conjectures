/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_weights08 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 33 1 32000 24 leaf00005_w_segment08)
theorem leaf00005_w_weights08_identity : leaf00005_w_weights08=IntegerWeightedOuter.weights 33 1 32000 24 leaf00005_w_segment08 := by decide +kernel
noncomputable def leaf00005_w_piece08 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00005_w_weights08 leaf00005_w_segment08)
theorem leaf00005_w_piece08_weighted : leaf00005_w_piece08=IntegerWeightedOuter.applyWeights leaf00005_w_weights08 leaf00005_w_segment08 := by decide +kernel
theorem leaf00005_w_piece08_identity : leaf00005_w_piece08=IntegerOuterTerms.transform 33 1 32000 24 leaf00005_w_segment08 :=
  IntegerWeightedOuter.checked 33 1 32000 24 leaf00005_w_segment08 leaf00005_w_piece08 leaf00005_w_weights08 leaf00005_w_weights08_identity leaf00005_w_piece08_weighted
#print axioms leaf00005_w_weights08_identity
#print axioms leaf00005_w_piece08_weighted
#print axioms leaf00005_w_piece08_identity
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
