/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01431RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01431_w_weights28 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 16 1 64 84 leaf01431_w_segment28)
theorem leaf01431_w_weights28_identity : leaf01431_w_weights28=IntegerWeightedOuter.weights 16 1 64 84 leaf01431_w_segment28 := by decide +kernel
noncomputable def leaf01431_w_piece28 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01431_w_weights28 leaf01431_w_segment28)
theorem leaf01431_w_piece28_weighted : leaf01431_w_piece28=IntegerWeightedOuter.applyWeights leaf01431_w_weights28 leaf01431_w_segment28 := by decide +kernel
theorem leaf01431_w_piece28_identity : leaf01431_w_piece28=IntegerOuterTerms.transform 16 1 64 84 leaf01431_w_segment28 :=
  IntegerWeightedOuter.checked 16 1 64 84 leaf01431_w_segment28 leaf01431_w_piece28 leaf01431_w_weights28 leaf01431_w_weights28_identity leaf01431_w_piece28_weighted
#print axioms leaf01431_w_weights28_identity
#print axioms leaf01431_w_piece28_weighted
#print axioms leaf01431_w_piece28_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
