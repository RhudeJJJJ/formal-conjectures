/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260SegmentedSources
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01260_w_weights01 : List (List ℤ) := rg_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 3 leaf01260_w_segment01)
theorem leaf01260_w_weights01_identity : leaf01260_w_weights01=IntegerWeightedOuter.weights 8 1 16 3 leaf01260_w_segment01 := by decide +kernel
def leaf01260_w_piece01 : NestedInteger.Poly 3 := rg_integer_data% (IntegerWeightedOuter.applyWeights leaf01260_w_weights01 leaf01260_w_segment01)
theorem leaf01260_w_piece01_weighted : leaf01260_w_piece01=IntegerWeightedOuter.applyWeights leaf01260_w_weights01 leaf01260_w_segment01 := by decide +kernel
theorem leaf01260_w_piece01_identity : leaf01260_w_piece01=IntegerOuterTerms.transform 8 1 16 3 leaf01260_w_segment01 :=
  IntegerWeightedOuter.checked 8 1 16 3 leaf01260_w_segment01 leaf01260_w_piece01 leaf01260_w_weights01 leaf01260_w_weights01_identity leaf01260_w_piece01_weighted
#print axioms leaf01260_w_weights01_identity
#print axioms leaf01260_w_piece01_weighted
#print axioms leaf01260_w_piece01_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
