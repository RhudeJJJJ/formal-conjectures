/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_weights15 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 45 leaf01260_w_segment15)
theorem leaf01260_w_weights15_identity : leaf01260_w_weights15=IntegerWeightedOuter.weights 8 1 16 45 leaf01260_w_segment15 := by decide +kernel
def leaf01260_w_piece15 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights15 leaf01260_w_segment15)
theorem leaf01260_w_piece15_weighted : leaf01260_w_piece15=IntegerWeightedOuter.applyWeights leaf01260_w_weights15 leaf01260_w_segment15 := by decide +kernel
theorem leaf01260_w_piece15_identity : leaf01260_w_piece15=IntegerOuterTerms.transform 8 1 16 45 leaf01260_w_segment15 :=
  IntegerWeightedOuter.checked 8 1 16 45 leaf01260_w_segment15 leaf01260_w_piece15 leaf01260_w_weights15 leaf01260_w_weights15_identity leaf01260_w_piece15_weighted
#print axioms leaf01260_w_weights15_identity
#print axioms leaf01260_w_piece15_weighted
#print axioms leaf01260_w_piece15_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
