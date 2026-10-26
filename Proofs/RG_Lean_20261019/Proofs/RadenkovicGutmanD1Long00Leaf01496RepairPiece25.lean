/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01496RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01496_w_weights25 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 12 1 64 75 leaf01496_w_segment25)
theorem leaf01496_w_weights25_identity : leaf01496_w_weights25=IntegerWeightedOuter.weights 12 1 64 75 leaf01496_w_segment25 := by decide +kernel
noncomputable def leaf01496_w_piece25 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01496_w_weights25 leaf01496_w_segment25)
theorem leaf01496_w_piece25_weighted : leaf01496_w_piece25=IntegerWeightedOuter.applyWeights leaf01496_w_weights25 leaf01496_w_segment25 := by decide +kernel
theorem leaf01496_w_piece25_identity : leaf01496_w_piece25=IntegerOuterTerms.transform 12 1 64 75 leaf01496_w_segment25 :=
  IntegerWeightedOuter.checked 12 1 64 75 leaf01496_w_segment25 leaf01496_w_piece25 leaf01496_w_weights25 leaf01496_w_weights25_identity leaf01496_w_piece25_weighted
#print axioms leaf01496_w_weights25_identity
#print axioms leaf01496_w_piece25_weighted
#print axioms leaf01496_w_piece25_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
