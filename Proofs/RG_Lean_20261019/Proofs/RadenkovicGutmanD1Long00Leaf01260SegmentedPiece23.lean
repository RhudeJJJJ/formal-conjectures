/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_weights23 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 69 leaf01260_w_segment23)
theorem leaf01260_w_weights23_identity : leaf01260_w_weights23=IntegerWeightedOuter.weights 8 1 16 69 leaf01260_w_segment23 := by decide +kernel
def leaf01260_w_piece23 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights23 leaf01260_w_segment23)
theorem leaf01260_w_piece23_weighted : leaf01260_w_piece23=IntegerWeightedOuter.applyWeights leaf01260_w_weights23 leaf01260_w_segment23 := by decide +kernel
theorem leaf01260_w_piece23_identity : leaf01260_w_piece23=IntegerOuterTerms.transform 8 1 16 69 leaf01260_w_segment23 :=
  IntegerWeightedOuter.checked 8 1 16 69 leaf01260_w_segment23 leaf01260_w_piece23 leaf01260_w_weights23 leaf01260_w_weights23_identity leaf01260_w_piece23_weighted
#print axioms leaf01260_w_weights23_identity
#print axioms leaf01260_w_piece23_weighted
#print axioms leaf01260_w_piece23_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
