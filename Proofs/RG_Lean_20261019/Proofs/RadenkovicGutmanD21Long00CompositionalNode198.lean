/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode197
import Proofs.RadenkovicGutmanD21Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[135,0],[0,0]],[[0,0],[0,0]],[[1763,0],[0,0]],[[0,0],[0,0]],[[10508,0],[0,0]],[[0,0],[0,0]],[[34767,0],[0,0]],[[0,0],[0,0]],[[68292,2],[2,0]],[[0,0],[0,0]],[[80492,79],[79,0]],[[0,0],[0,0]],[[54976,506],[506,0]],[[0,0],[0,0]],[[19389,1182],[1182,0]],[[0,0],[0,0]],[[2313,1068],[1068,0]],[[0,0],[0,0]],[[-189,315],[315,2]],[[0],[0,0]],[[0],[0,21]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
