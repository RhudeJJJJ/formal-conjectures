/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3FullParameterGroup0000Sources
import Proofs.RadenkovicGutmanClosedIntegerRowElaboration
namespace Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
noncomputable def leaf00000_w_weights02 : List (List ℤ) := rg_closed_integer_row%
  (IntegerWeightedOuter.weights 32 1 32000 6 leaf00000_w_segment02)
theorem leaf00000_w_weights02_identity : leaf00000_w_weights02=IntegerWeightedOuter.weights 32 1 32000 6 leaf00000_w_segment02 := by decide +kernel
noncomputable def leaf00000_w_piece02 : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerWeightedOuter.applyWeights leaf00000_w_weights02 leaf00000_w_segment02)
theorem leaf00000_w_piece02_weighted : leaf00000_w_piece02=IntegerWeightedOuter.applyWeights leaf00000_w_weights02 leaf00000_w_segment02 := by decide +kernel
theorem leaf00000_w_piece02_identity : leaf00000_w_piece02=IntegerOuterTerms.transform 32 1 32000 6 leaf00000_w_segment02 :=
  IntegerWeightedOuter.checked 32 1 32000 6 leaf00000_w_segment02 leaf00000_w_piece02 leaf00000_w_weights02 leaf00000_w_weights02_identity leaf00000_w_piece02_weighted
#print axioms leaf00000_w_weights02_identity
#print axioms leaf00000_w_piece02_weighted
#print axioms leaf00000_w_piece02_identity
end Gebendorfer.RadenkovicGutman.D3FullParameterGroup0000
