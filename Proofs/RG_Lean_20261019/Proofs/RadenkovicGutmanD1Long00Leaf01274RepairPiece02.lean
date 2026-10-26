/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01274RepairSources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf01274_w_weights02 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 8 1 16 6 leaf01274_w_segment02)
theorem leaf01274_w_weights02_identity : leaf01274_w_weights02=IntegerWeightedOuter.weights 8 1 16 6 leaf01274_w_segment02 := by decide +kernel
noncomputable def leaf01274_w_piece02 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf01274_w_weights02 leaf01274_w_segment02)
theorem leaf01274_w_piece02_weighted : leaf01274_w_piece02=IntegerWeightedOuter.applyWeights leaf01274_w_weights02 leaf01274_w_segment02 := by decide +kernel
theorem leaf01274_w_piece02_identity : leaf01274_w_piece02=IntegerOuterTerms.transform 8 1 16 6 leaf01274_w_segment02 :=
  IntegerWeightedOuter.checked 8 1 16 6 leaf01274_w_segment02 leaf01274_w_piece02 leaf01274_w_weights02 leaf01274_w_weights02_identity leaf01274_w_piece02_weighted
#print axioms leaf01274_w_weights02_identity
#print axioms leaf01274_w_piece02_weighted
#print axioms leaf01274_w_piece02_identity
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
