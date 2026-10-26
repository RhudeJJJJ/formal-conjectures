/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01262RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01262_w_weights28 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 84 leaf01262_w_segment28)
theorem leaf01262_w_weights28_identity : leaf01262_w_weights28=IntegerWeightedOuter.weights 8 1 16 84 leaf01262_w_segment28 := by decide +kernel
noncomputable def leaf01262_w_piece28 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01262_w_weights28 leaf01262_w_segment28)
theorem leaf01262_w_piece28_weighted : leaf01262_w_piece28=IntegerWeightedOuter.applyWeights leaf01262_w_weights28 leaf01262_w_segment28 := by decide +kernel
theorem leaf01262_w_piece28_identity : leaf01262_w_piece28=IntegerOuterTerms.transform 8 1 16 84 leaf01262_w_segment28 :=
  IntegerWeightedOuter.checked 8 1 16 84 leaf01262_w_segment28 leaf01262_w_piece28 leaf01262_w_weights28 leaf01262_w_weights28_identity leaf01262_w_piece28_weighted
#print axioms leaf01262_w_weights28_identity
#print axioms leaf01262_w_piece28_weighted
#print axioms leaf01262_w_piece28_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
