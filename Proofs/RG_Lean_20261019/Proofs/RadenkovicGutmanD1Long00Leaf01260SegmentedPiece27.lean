/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_weights27 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 81 leaf01260_w_segment27)
theorem leaf01260_w_weights27_identity : leaf01260_w_weights27=IntegerWeightedOuter.weights 8 1 16 81 leaf01260_w_segment27 := by decide +kernel
def leaf01260_w_piece27 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights27 leaf01260_w_segment27)
theorem leaf01260_w_piece27_weighted : leaf01260_w_piece27=IntegerWeightedOuter.applyWeights leaf01260_w_weights27 leaf01260_w_segment27 := by decide +kernel
theorem leaf01260_w_piece27_identity : leaf01260_w_piece27=IntegerOuterTerms.transform 8 1 16 81 leaf01260_w_segment27 :=
  IntegerWeightedOuter.checked 8 1 16 81 leaf01260_w_segment27 leaf01260_w_piece27 leaf01260_w_weights27 leaf01260_w_weights27_identity leaf01260_w_piece27_weighted
#print axioms leaf01260_w_weights27_identity
#print axioms leaf01260_w_piece27_weighted
#print axioms leaf01260_w_piece27_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
