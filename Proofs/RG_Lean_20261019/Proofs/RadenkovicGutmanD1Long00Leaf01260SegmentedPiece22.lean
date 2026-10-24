/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_weights22 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 66 leaf01260_w_segment22)
theorem leaf01260_w_weights22_identity : leaf01260_w_weights22=IntegerWeightedOuter.weights 8 1 16 66 leaf01260_w_segment22 := by decide +kernel
def leaf01260_w_piece22 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights22 leaf01260_w_segment22)
theorem leaf01260_w_piece22_weighted : leaf01260_w_piece22=IntegerWeightedOuter.applyWeights leaf01260_w_weights22 leaf01260_w_segment22 := by decide +kernel
theorem leaf01260_w_piece22_identity : leaf01260_w_piece22=IntegerOuterTerms.transform 8 1 16 66 leaf01260_w_segment22 :=
  IntegerWeightedOuter.checked 8 1 16 66 leaf01260_w_segment22 leaf01260_w_piece22 leaf01260_w_weights22 leaf01260_w_weights22_identity leaf01260_w_piece22_weighted
#print axioms leaf01260_w_weights22_identity
#print axioms leaf01260_w_piece22_weighted
#print axioms leaf01260_w_piece22_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
