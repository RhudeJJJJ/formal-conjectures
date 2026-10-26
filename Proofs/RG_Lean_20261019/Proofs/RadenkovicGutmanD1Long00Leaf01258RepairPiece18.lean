/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01258RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01258_w_weights18 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 54 leaf01258_w_segment18)
theorem leaf01258_w_weights18_identity : leaf01258_w_weights18=IntegerWeightedOuter.weights 8 1 16 54 leaf01258_w_segment18 := by decide +kernel
noncomputable def leaf01258_w_piece18 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01258_w_weights18 leaf01258_w_segment18)
theorem leaf01258_w_piece18_weighted : leaf01258_w_piece18=IntegerWeightedOuter.applyWeights leaf01258_w_weights18 leaf01258_w_segment18 := by decide +kernel
theorem leaf01258_w_piece18_identity : leaf01258_w_piece18=IntegerOuterTerms.transform 8 1 16 54 leaf01258_w_segment18 :=
  IntegerWeightedOuter.checked 8 1 16 54 leaf01258_w_segment18 leaf01258_w_piece18 leaf01258_w_weights18 leaf01258_w_weights18_identity leaf01258_w_piece18_weighted
#print axioms leaf01258_w_weights18_identity
#print axioms leaf01258_w_piece18_weighted
#print axioms leaf01258_w_piece18_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
