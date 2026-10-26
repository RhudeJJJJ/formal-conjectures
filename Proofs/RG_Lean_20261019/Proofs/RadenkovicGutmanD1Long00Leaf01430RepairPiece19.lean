/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01430RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01430_w_weights19 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 16 1 64 57 leaf01430_w_segment19)
theorem leaf01430_w_weights19_identity : leaf01430_w_weights19=IntegerWeightedOuter.weights 16 1 64 57 leaf01430_w_segment19 := by decide +kernel
noncomputable def leaf01430_w_piece19 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01430_w_weights19 leaf01430_w_segment19)
theorem leaf01430_w_piece19_weighted : leaf01430_w_piece19=IntegerWeightedOuter.applyWeights leaf01430_w_weights19 leaf01430_w_segment19 := by decide +kernel
theorem leaf01430_w_piece19_identity : leaf01430_w_piece19=IntegerOuterTerms.transform 16 1 64 57 leaf01430_w_segment19 :=
  IntegerWeightedOuter.checked 16 1 64 57 leaf01430_w_segment19 leaf01430_w_piece19 leaf01430_w_weights19 leaf01430_w_weights19_identity leaf01430_w_piece19_weighted
#print axioms leaf01430_w_weights19_identity
#print axioms leaf01430_w_piece19_weighted
#print axioms leaf01430_w_piece19_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
