/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_weights28 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 84 leaf01260_w_segment28)
theorem leaf01260_w_weights28_identity : leaf01260_w_weights28=IntegerWeightedOuter.weights 8 1 16 84 leaf01260_w_segment28 := by decide +kernel
def leaf01260_w_piece28 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights28 leaf01260_w_segment28)
theorem leaf01260_w_piece28_weighted : leaf01260_w_piece28=IntegerWeightedOuter.applyWeights leaf01260_w_weights28 leaf01260_w_segment28 := by decide +kernel
theorem leaf01260_w_piece28_identity : leaf01260_w_piece28=IntegerOuterTerms.transform 8 1 16 84 leaf01260_w_segment28 :=
  IntegerWeightedOuter.checked 8 1 16 84 leaf01260_w_segment28 leaf01260_w_piece28 leaf01260_w_weights28 leaf01260_w_weights28_identity leaf01260_w_piece28_weighted
#print axioms leaf01260_w_weights28_identity
#print axioms leaf01260_w_piece28_weighted
#print axioms leaf01260_w_piece28_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
