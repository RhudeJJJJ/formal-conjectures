/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01292RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01292_w_weights28 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 14 1 32 84 leaf01292_w_segment28)
theorem leaf01292_w_weights28_identity : leaf01292_w_weights28=IntegerWeightedOuter.weights 14 1 32 84 leaf01292_w_segment28 := by decide +kernel
noncomputable def leaf01292_w_piece28 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01292_w_weights28 leaf01292_w_segment28)
theorem leaf01292_w_piece28_weighted : leaf01292_w_piece28=IntegerWeightedOuter.applyWeights leaf01292_w_weights28 leaf01292_w_segment28 := by decide +kernel
theorem leaf01292_w_piece28_identity : leaf01292_w_piece28=IntegerOuterTerms.transform 14 1 32 84 leaf01292_w_segment28 :=
  IntegerWeightedOuter.checked 14 1 32 84 leaf01292_w_segment28 leaf01292_w_piece28 leaf01292_w_weights28 leaf01292_w_weights28_identity leaf01292_w_piece28_weighted
#print axioms leaf01292_w_weights28_identity
#print axioms leaf01292_w_piece28_weighted
#print axioms leaf01292_w_piece28_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
