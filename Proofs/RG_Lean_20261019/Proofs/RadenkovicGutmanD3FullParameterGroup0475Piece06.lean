/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0475Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01900_w_weights06 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 559 3 12800 18 leaf01900_w_segment06)
theorem leaf01900_w_weights06_identity : leaf01900_w_weights06=IntegerWeightedOuter.weights 559 3 12800 18 leaf01900_w_segment06 := by decide +kernel
noncomputable def leaf01900_w_piece06 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01900_w_weights06 leaf01900_w_segment06)
theorem leaf01900_w_piece06_weighted : leaf01900_w_piece06=IntegerWeightedOuter.applyWeights leaf01900_w_weights06 leaf01900_w_segment06 := by decide +kernel
theorem leaf01900_w_piece06_identity : leaf01900_w_piece06=IntegerOuterTerms.transform 559 3 12800 18 leaf01900_w_segment06 :=
  IntegerWeightedOuter.checked 559 3 12800 18 leaf01900_w_segment06 leaf01900_w_piece06 leaf01900_w_weights06 leaf01900_w_weights06_identity leaf01900_w_piece06_weighted
#print axioms leaf01900_w_weights06_identity
#print axioms leaf01900_w_piece06_weighted
#print axioms leaf01900_w_piece06_identity
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0475
