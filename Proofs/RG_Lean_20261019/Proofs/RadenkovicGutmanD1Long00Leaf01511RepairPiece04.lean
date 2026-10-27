/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01511RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01511_w_weights04 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 12 1 64 12 leaf01511_w_segment04)
theorem leaf01511_w_weights04_identity : leaf01511_w_weights04=IntegerWeightedOuter.weights 12 1 64 12 leaf01511_w_segment04 := by decide +kernel
noncomputable def leaf01511_w_piece04 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01511_w_weights04 leaf01511_w_segment04)
theorem leaf01511_w_piece04_weighted : leaf01511_w_piece04=IntegerWeightedOuter.applyWeights leaf01511_w_weights04 leaf01511_w_segment04 := by decide +kernel
theorem leaf01511_w_piece04_identity : leaf01511_w_piece04=IntegerOuterTerms.transform 12 1 64 12 leaf01511_w_segment04 :=
  IntegerWeightedOuter.checked 12 1 64 12 leaf01511_w_segment04 leaf01511_w_piece04 leaf01511_w_weights04 leaf01511_w_weights04_identity leaf01511_w_piece04_weighted
#print axioms leaf01511_w_weights04_identity
#print axioms leaf01511_w_piece04_weighted
#print axioms leaf01511_w_piece04_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
