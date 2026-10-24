/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_weights07 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 21 leaf01260_w_segment07)
theorem leaf01260_w_weights07_identity : leaf01260_w_weights07=IntegerWeightedOuter.weights 8 1 16 21 leaf01260_w_segment07 := by decide +kernel
def leaf01260_w_piece07 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights07 leaf01260_w_segment07)
theorem leaf01260_w_piece07_weighted : leaf01260_w_piece07=IntegerWeightedOuter.applyWeights leaf01260_w_weights07 leaf01260_w_segment07 := by decide +kernel
theorem leaf01260_w_piece07_identity : leaf01260_w_piece07=IntegerOuterTerms.transform 8 1 16 21 leaf01260_w_segment07 :=
  IntegerWeightedOuter.checked 8 1 16 21 leaf01260_w_segment07 leaf01260_w_piece07 leaf01260_w_weights07 leaf01260_w_weights07_identity leaf01260_w_piece07_weighted
#print axioms leaf01260_w_weights07_identity
#print axioms leaf01260_w_piece07_weighted
#print axioms leaf01260_w_piece07_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
