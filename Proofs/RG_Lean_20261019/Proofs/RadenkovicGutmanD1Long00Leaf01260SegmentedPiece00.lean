/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_weights00 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 0 leaf01260_w_segment00)
theorem leaf01260_w_weights00_identity : leaf01260_w_weights00=IntegerWeightedOuter.weights 8 1 16 0 leaf01260_w_segment00 := by decide +kernel
def leaf01260_w_piece00 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights00 leaf01260_w_segment00)
theorem leaf01260_w_piece00_weighted : leaf01260_w_piece00=IntegerWeightedOuter.applyWeights leaf01260_w_weights00 leaf01260_w_segment00 := by decide +kernel
theorem leaf01260_w_piece00_identity : leaf01260_w_piece00=IntegerOuterTerms.transform 8 1 16 0 leaf01260_w_segment00 :=
  IntegerWeightedOuter.checked 8 1 16 0 leaf01260_w_segment00 leaf01260_w_piece00 leaf01260_w_weights00 leaf01260_w_weights00_identity leaf01260_w_piece00_weighted
#print axioms leaf01260_w_weights00_identity
#print axioms leaf01260_w_piece00_weighted
#print axioms leaf01260_w_piece00_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
