/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2FullParameterGroup0001Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00005_w_weights00 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 33 1 32000 0 leaf00005_w_segment00)
theorem leaf00005_w_weights00_identity : leaf00005_w_weights00=IntegerWeightedOuter.weights 33 1 32000 0 leaf00005_w_segment00 := by decide +kernel
noncomputable def leaf00005_w_piece00 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00005_w_weights00 leaf00005_w_segment00)
theorem leaf00005_w_piece00_weighted : leaf00005_w_piece00=IntegerWeightedOuter.applyWeights leaf00005_w_weights00 leaf00005_w_segment00 := by decide +kernel
theorem leaf00005_w_piece00_identity : leaf00005_w_piece00=IntegerOuterTerms.transform 33 1 32000 0 leaf00005_w_segment00 :=
  IntegerWeightedOuter.checked 33 1 32000 0 leaf00005_w_segment00 leaf00005_w_piece00 leaf00005_w_weights00 leaf00005_w_weights00_identity leaf00005_w_piece00_weighted
#print axioms leaf00005_w_weights00_identity
#print axioms leaf00005_w_piece00_weighted
#print axioms leaf00005_w_piece00_identity
end Gebendorfer.RadenkovicGutman.D2FullParameterGroup0001
