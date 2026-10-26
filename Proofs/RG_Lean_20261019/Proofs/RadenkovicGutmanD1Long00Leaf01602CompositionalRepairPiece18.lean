/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01602CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01602_w_weights18 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 16 1 128 54 leaf01602_w_segment18)
theorem leaf01602_w_weights18_identity : leaf01602_w_weights18=IntegerWeightedOuter.weights 16 1 128 54 leaf01602_w_segment18 := by decide +kernel
noncomputable def leaf01602_w_piece18 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01602_w_weights18 leaf01602_w_segment18)
theorem leaf01602_w_piece18_weighted : leaf01602_w_piece18=IntegerWeightedOuter.applyWeights leaf01602_w_weights18 leaf01602_w_segment18 := by decide +kernel
theorem leaf01602_w_piece18_identity : leaf01602_w_piece18=IntegerOuterTerms.transform 16 1 128 54 leaf01602_w_segment18 :=
  IntegerWeightedOuter.checked 16 1 128 54 leaf01602_w_segment18 leaf01602_w_piece18 leaf01602_w_weights18 leaf01602_w_weights18_identity leaf01602_w_piece18_weighted
#print axioms leaf01602_w_weights18_identity
#print axioms leaf01602_w_piece18_weighted
#print axioms leaf01602_w_piece18_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
