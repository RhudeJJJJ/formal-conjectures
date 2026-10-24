/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_weights09 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 27 leaf01260_w_segment09)
theorem leaf01260_w_weights09_identity : leaf01260_w_weights09=IntegerWeightedOuter.weights 8 1 16 27 leaf01260_w_segment09 := by decide +kernel
def leaf01260_w_piece09 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights09 leaf01260_w_segment09)
theorem leaf01260_w_piece09_weighted : leaf01260_w_piece09=IntegerWeightedOuter.applyWeights leaf01260_w_weights09 leaf01260_w_segment09 := by decide +kernel
theorem leaf01260_w_piece09_identity : leaf01260_w_piece09=IntegerOuterTerms.transform 8 1 16 27 leaf01260_w_segment09 :=
  IntegerWeightedOuter.checked 8 1 16 27 leaf01260_w_segment09 leaf01260_w_piece09 leaf01260_w_weights09 leaf01260_w_weights09_identity leaf01260_w_piece09_weighted
#print axioms leaf01260_w_weights09_identity
#print axioms leaf01260_w_piece09_weighted
#print axioms leaf01260_w_piece09_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
