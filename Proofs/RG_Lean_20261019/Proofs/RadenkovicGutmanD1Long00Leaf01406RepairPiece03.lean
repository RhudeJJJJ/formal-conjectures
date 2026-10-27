/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01406RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01406_w_weights03 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 18 1 64 9 leaf01406_w_segment03)
theorem leaf01406_w_weights03_identity : leaf01406_w_weights03=IntegerWeightedOuter.weights 18 1 64 9 leaf01406_w_segment03 := by decide +kernel
noncomputable def leaf01406_w_piece03 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01406_w_weights03 leaf01406_w_segment03)
theorem leaf01406_w_piece03_weighted : leaf01406_w_piece03=IntegerWeightedOuter.applyWeights leaf01406_w_weights03 leaf01406_w_segment03 := by decide +kernel
theorem leaf01406_w_piece03_identity : leaf01406_w_piece03=IntegerOuterTerms.transform 18 1 64 9 leaf01406_w_segment03 :=
  IntegerWeightedOuter.checked 18 1 64 9 leaf01406_w_segment03 leaf01406_w_piece03 leaf01406_w_weights03 leaf01406_w_weights03_identity leaf01406_w_piece03_weighted
#print axioms leaf01406_w_weights03_identity
#print axioms leaf01406_w_piece03_weighted
#print axioms leaf01406_w_piece03_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
