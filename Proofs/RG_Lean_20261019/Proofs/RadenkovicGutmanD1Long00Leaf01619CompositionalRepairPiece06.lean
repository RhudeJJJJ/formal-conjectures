/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01619CompositionalRepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01619_w_weights06 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 15 1 128 18 leaf01619_w_segment06)
theorem leaf01619_w_weights06_identity : leaf01619_w_weights06=IntegerWeightedOuter.weights 15 1 128 18 leaf01619_w_segment06 := by decide +kernel
noncomputable def leaf01619_w_piece06 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01619_w_weights06 leaf01619_w_segment06)
theorem leaf01619_w_piece06_weighted : leaf01619_w_piece06=IntegerWeightedOuter.applyWeights leaf01619_w_weights06 leaf01619_w_segment06 := by decide +kernel
theorem leaf01619_w_piece06_identity : leaf01619_w_piece06=IntegerOuterTerms.transform 15 1 128 18 leaf01619_w_segment06 :=
  IntegerWeightedOuter.checked 15 1 128 18 leaf01619_w_segment06 leaf01619_w_piece06 leaf01619_w_weights06 leaf01619_w_weights06_identity leaf01619_w_piece06_weighted
#print axioms leaf01619_w_weights06_identity
#print axioms leaf01619_w_piece06_weighted
#print axioms leaf01619_w_piece06_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
