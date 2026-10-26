/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01265RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01265_w_weights17 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 51 leaf01265_w_segment17)
theorem leaf01265_w_weights17_identity : leaf01265_w_weights17=IntegerWeightedOuter.weights 8 1 16 51 leaf01265_w_segment17 := by decide +kernel
noncomputable def leaf01265_w_piece17 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01265_w_weights17 leaf01265_w_segment17)
theorem leaf01265_w_piece17_weighted : leaf01265_w_piece17=IntegerWeightedOuter.applyWeights leaf01265_w_weights17 leaf01265_w_segment17 := by decide +kernel
theorem leaf01265_w_piece17_identity : leaf01265_w_piece17=IntegerOuterTerms.transform 8 1 16 51 leaf01265_w_segment17 :=
  IntegerWeightedOuter.checked 8 1 16 51 leaf01265_w_segment17 leaf01265_w_piece17 leaf01265_w_weights17 leaf01265_w_weights17_identity leaf01265_w_piece17_weighted
#print axioms leaf01265_w_weights17_identity
#print axioms leaf01265_w_piece17_weighted
#print axioms leaf01265_w_piece17_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
