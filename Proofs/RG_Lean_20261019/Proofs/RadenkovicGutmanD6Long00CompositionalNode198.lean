/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode197
import Proofs.RadenkovicGutmanD6Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[60,0],[0,0]],[[0,0],[0,0]],[[638,0],[0,0]],[[0,0],[0,0]],[[3458,0],[0,0]],[[0,0],[0,0]],[[10842,0],[0,0]],[[0,0],[0,0]],[[20592,2],[2,0]],[[0,0],[0,0]],[[23732,34],[34,0]],[[0,0],[0,0]],[[15946,176],[176,0]],[[0,0],[0,0]],[[5544,372],[372,0]],[[0,0],[0,0]],[[648,318],[318,0]],[[0,0],[0,0]],[[-54,90],[90,2]],[[0],[0,0]],[[0],[0,6]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
