/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01266RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01266_w_weights00 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 0 leaf01266_w_segment00)
theorem leaf01266_w_weights00_identity : leaf01266_w_weights00=IntegerWeightedOuter.weights 8 1 16 0 leaf01266_w_segment00 := by decide +kernel
noncomputable def leaf01266_w_piece00 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01266_w_weights00 leaf01266_w_segment00)
theorem leaf01266_w_piece00_weighted : leaf01266_w_piece00=IntegerWeightedOuter.applyWeights leaf01266_w_weights00 leaf01266_w_segment00 := by decide +kernel
theorem leaf01266_w_piece00_identity : leaf01266_w_piece00=IntegerOuterTerms.transform 8 1 16 0 leaf01266_w_segment00 :=
  IntegerWeightedOuter.checked 8 1 16 0 leaf01266_w_segment00 leaf01266_w_piece00 leaf01266_w_weights00 leaf01266_w_weights00_identity leaf01266_w_piece00_weighted
#print axioms leaf01266_w_weights00_identity
#print axioms leaf01266_w_piece00_weighted
#print axioms leaf01266_w_piece00_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
