/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01339RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01339_w_weights13 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 12 1 32 39 leaf01339_w_segment13)
theorem leaf01339_w_weights13_identity : leaf01339_w_weights13=IntegerWeightedOuter.weights 12 1 32 39 leaf01339_w_segment13 := by decide +kernel
noncomputable def leaf01339_w_piece13 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01339_w_weights13 leaf01339_w_segment13)
theorem leaf01339_w_piece13_weighted : leaf01339_w_piece13=IntegerWeightedOuter.applyWeights leaf01339_w_weights13 leaf01339_w_segment13 := by decide +kernel
theorem leaf01339_w_piece13_identity : leaf01339_w_piece13=IntegerOuterTerms.transform 12 1 32 39 leaf01339_w_segment13 :=
  IntegerWeightedOuter.checked 12 1 32 39 leaf01339_w_segment13 leaf01339_w_piece13 leaf01339_w_weights13 leaf01339_w_weights13_identity leaf01339_w_piece13_weighted
#print axioms leaf01339_w_weights13_identity
#print axioms leaf01339_w_piece13_weighted
#print axioms leaf01339_w_piece13_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
