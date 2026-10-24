/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260NoRuntimeSegmentedJoin27
import Proofs.RadenkovicGutmanIntegerOuterJoinedEvaluation
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 100

theorem leaf01260_compositional_suffix27_eval (x : Fin 3 → ℝ) :
    NestedHorner.eval (NestedInteger.castPoly 3 leaf01260_w_suffix27) x=
      NestedHorner.eval (NestedInteger.castPoly 3
        (IntegerOuterTerms.transform 8 1 16 81 leaf01260_w_source27)) x :=
  IntegerOuterJoinedEvaluation.joined 8 1 16 81 84
    leaf01260_w_segment27 leaf01260_w_source28 leaf01260_w_source27
    leaf01260_w_piece27 leaf01260_w_suffix28 leaf01260_w_suffix27
    (by decide +kernel) (List.take_append_drop 3 leaf01260_w_source27)
    leaf01260_w_piece27_identity leaf01260_w_suffix28_eval leaf01260_w_suffix27_join x

#print axioms leaf01260_compositional_suffix27_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
