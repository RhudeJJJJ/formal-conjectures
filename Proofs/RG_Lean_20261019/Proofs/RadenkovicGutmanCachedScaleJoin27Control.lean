/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Long00Leaf01260CompositionalRepairJoin27

namespace Gebendorfer.RadenkovicGutman.CachedScaleJoin27Control
open DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def factor : ℤ := 1048576

/-- The original suffix length and denominator remain kernel checked once. -/
theorem factor_checked : factor=16^leaf01260_w_source28.length := by decide +kernel

/-- Recheck the actual original integer vectors with the checked scalar. -/
theorem arithmetic_checked :
    leaf01260_w_suffix27=NestedInteger.add
      (NestedInteger.scale factor leaf01260_w_piece27) leaf01260_w_suffix28 := by
  decide +kernel

/-- The original join statement is recovered by congruence, without using its
previous proof or reevaluating the scalar under every coefficient. -/
theorem original_join_checked :
    leaf01260_w_suffix27=NestedInteger.add
      (NestedInteger.scale (16^leaf01260_w_source28.length) leaf01260_w_piece27)
      leaf01260_w_suffix28 :=
  arithmetic_checked.trans (congrArg
    (fun z : ℤ => NestedInteger.add (NestedInteger.scale z leaf01260_w_piece27)
      leaf01260_w_suffix28) factor_checked)

#print axioms factor_checked
#print axioms arithmetic_checked
#print axioms original_join_checked
end Gebendorfer.RadenkovicGutman.CachedScaleJoin27Control
