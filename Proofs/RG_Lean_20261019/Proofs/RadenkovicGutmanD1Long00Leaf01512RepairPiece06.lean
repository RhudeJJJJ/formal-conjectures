/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01512RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01512_w_weights06 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 12 1 64 18 leaf01512_w_segment06)
theorem leaf01512_w_weights06_identity : leaf01512_w_weights06=IntegerWeightedOuter.weights 12 1 64 18 leaf01512_w_segment06 := by decide +kernel
noncomputable def leaf01512_w_piece06 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01512_w_weights06 leaf01512_w_segment06)
theorem leaf01512_w_piece06_weighted : leaf01512_w_piece06=IntegerWeightedOuter.applyWeights leaf01512_w_weights06 leaf01512_w_segment06 := by decide +kernel
theorem leaf01512_w_piece06_identity : leaf01512_w_piece06=IntegerOuterTerms.transform 12 1 64 18 leaf01512_w_segment06 :=
  IntegerWeightedOuter.checked 12 1 64 18 leaf01512_w_segment06 leaf01512_w_piece06 leaf01512_w_weights06 leaf01512_w_weights06_identity leaf01512_w_piece06_weighted
#print axioms leaf01512_w_weights06_identity
#print axioms leaf01512_w_piece06_weighted
#print axioms leaf01512_w_piece06_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
