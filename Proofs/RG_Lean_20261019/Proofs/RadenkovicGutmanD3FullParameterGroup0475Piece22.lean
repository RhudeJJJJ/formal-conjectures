/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_weights22 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 559 3 12800 66 leaf01900_w_segment22)
theorem leaf01900_w_weights22_identity : leaf01900_w_weights22=IntegerWeightedOuter.weights 559 3 12800 66 leaf01900_w_segment22 := by decide +kernel
noncomputable def leaf01900_w_piece22 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01900_w_weights22 leaf01900_w_segment22)
theorem leaf01900_w_piece22_weighted : leaf01900_w_piece22=IntegerWeightedOuter.applyWeights leaf01900_w_weights22 leaf01900_w_segment22 := by decide +kernel
theorem leaf01900_w_piece22_identity : leaf01900_w_piece22=IntegerOuterTerms.transform 559 3 12800 66 leaf01900_w_segment22 :=
  IntegerWeightedOuter.checked 559 3 12800 66 leaf01900_w_segment22 leaf01900_w_piece22 leaf01900_w_weights22 leaf01900_w_weights22_identity leaf01900_w_piece22_weighted
#print axioms leaf01900_w_weights22_identity
#print axioms leaf01900_w_piece22_weighted
#print axioms leaf01900_w_piece22_identity
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
