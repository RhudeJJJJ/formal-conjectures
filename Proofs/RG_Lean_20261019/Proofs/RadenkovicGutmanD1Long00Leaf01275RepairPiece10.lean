/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01275RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01275_w_weights10 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 15 1 32 30 leaf01275_w_segment10)
theorem leaf01275_w_weights10_identity : leaf01275_w_weights10=IntegerWeightedOuter.weights 15 1 32 30 leaf01275_w_segment10 := by decide +kernel
noncomputable def leaf01275_w_piece10 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01275_w_weights10 leaf01275_w_segment10)
theorem leaf01275_w_piece10_weighted : leaf01275_w_piece10=IntegerWeightedOuter.applyWeights leaf01275_w_weights10 leaf01275_w_segment10 := by decide +kernel
theorem leaf01275_w_piece10_identity : leaf01275_w_piece10=IntegerOuterTerms.transform 15 1 32 30 leaf01275_w_segment10 :=
  IntegerWeightedOuter.checked 15 1 32 30 leaf01275_w_segment10 leaf01275_w_piece10 leaf01275_w_weights10 leaf01275_w_weights10_identity leaf01275_w_piece10_weighted
#print axioms leaf01275_w_weights10_identity
#print axioms leaf01275_w_piece10_weighted
#print axioms leaf01275_w_piece10_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
