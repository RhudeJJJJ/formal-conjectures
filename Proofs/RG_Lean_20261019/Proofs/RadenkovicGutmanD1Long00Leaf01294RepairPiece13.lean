/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01294RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01294_w_weights13 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 14 1 32 39 leaf01294_w_segment13)
theorem leaf01294_w_weights13_identity : leaf01294_w_weights13=IntegerWeightedOuter.weights 14 1 32 39 leaf01294_w_segment13 := by decide +kernel
noncomputable def leaf01294_w_piece13 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01294_w_weights13 leaf01294_w_segment13)
theorem leaf01294_w_piece13_weighted : leaf01294_w_piece13=IntegerWeightedOuter.applyWeights leaf01294_w_weights13 leaf01294_w_segment13 := by decide +kernel
theorem leaf01294_w_piece13_identity : leaf01294_w_piece13=IntegerOuterTerms.transform 14 1 32 39 leaf01294_w_segment13 :=
  IntegerWeightedOuter.checked 14 1 32 39 leaf01294_w_segment13 leaf01294_w_piece13 leaf01294_w_weights13 leaf01294_w_weights13_identity leaf01294_w_piece13_weighted
#print axioms leaf01294_w_weights13_identity
#print axioms leaf01294_w_piece13_weighted
#print axioms leaf01294_w_piece13_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
