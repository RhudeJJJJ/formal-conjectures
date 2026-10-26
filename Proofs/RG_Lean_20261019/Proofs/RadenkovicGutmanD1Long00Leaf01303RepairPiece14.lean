/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01303RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01303_w_weights14 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 14 1 32 42 leaf01303_w_segment14)
theorem leaf01303_w_weights14_identity : leaf01303_w_weights14=IntegerWeightedOuter.weights 14 1 32 42 leaf01303_w_segment14 := by decide +kernel
noncomputable def leaf01303_w_piece14 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01303_w_weights14 leaf01303_w_segment14)
theorem leaf01303_w_piece14_weighted : leaf01303_w_piece14=IntegerWeightedOuter.applyWeights leaf01303_w_weights14 leaf01303_w_segment14 := by decide +kernel
theorem leaf01303_w_piece14_identity : leaf01303_w_piece14=IntegerOuterTerms.transform 14 1 32 42 leaf01303_w_segment14 :=
  IntegerWeightedOuter.checked 14 1 32 42 leaf01303_w_segment14 leaf01303_w_piece14 leaf01303_w_weights14 leaf01303_w_weights14_identity leaf01303_w_piece14_weighted
#print axioms leaf01303_w_weights14_identity
#print axioms leaf01303_w_piece14_weighted
#print axioms leaf01303_w_piece14_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
