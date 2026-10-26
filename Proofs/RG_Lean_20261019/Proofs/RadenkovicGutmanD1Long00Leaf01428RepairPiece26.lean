/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01428RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01428_w_weights26 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 16 1 64 78 leaf01428_w_segment26)
theorem leaf01428_w_weights26_identity : leaf01428_w_weights26=IntegerWeightedOuter.weights 16 1 64 78 leaf01428_w_segment26 := by decide +kernel
noncomputable def leaf01428_w_piece26 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01428_w_weights26 leaf01428_w_segment26)
theorem leaf01428_w_piece26_weighted : leaf01428_w_piece26=IntegerWeightedOuter.applyWeights leaf01428_w_weights26 leaf01428_w_segment26 := by decide +kernel
theorem leaf01428_w_piece26_identity : leaf01428_w_piece26=IntegerOuterTerms.transform 16 1 64 78 leaf01428_w_segment26 :=
  IntegerWeightedOuter.checked 16 1 64 78 leaf01428_w_segment26 leaf01428_w_piece26 leaf01428_w_weights26 leaf01428_w_weights26_identity leaf01428_w_piece26_weighted
#print axioms leaf01428_w_weights26_identity
#print axioms leaf01428_w_piece26_weighted
#print axioms leaf01428_w_piece26_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
