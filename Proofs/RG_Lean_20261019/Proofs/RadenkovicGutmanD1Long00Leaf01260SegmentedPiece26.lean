/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_weights26 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 78 leaf01260_w_segment26)
theorem leaf01260_w_weights26_identity : leaf01260_w_weights26=IntegerWeightedOuter.weights 8 1 16 78 leaf01260_w_segment26 := by decide +kernel
def leaf01260_w_piece26 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights26 leaf01260_w_segment26)
theorem leaf01260_w_piece26_weighted : leaf01260_w_piece26=IntegerWeightedOuter.applyWeights leaf01260_w_weights26 leaf01260_w_segment26 := by decide +kernel
theorem leaf01260_w_piece26_identity : leaf01260_w_piece26=IntegerOuterTerms.transform 8 1 16 78 leaf01260_w_segment26 :=
  IntegerWeightedOuter.checked 8 1 16 78 leaf01260_w_segment26 leaf01260_w_piece26 leaf01260_w_weights26 leaf01260_w_weights26_identity leaf01260_w_piece26_weighted
#print axioms leaf01260_w_weights26_identity
#print axioms leaf01260_w_piece26_weighted
#print axioms leaf01260_w_piece26_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
