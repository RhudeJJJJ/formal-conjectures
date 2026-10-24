/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode199
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e200 : NestedArithmetic.Expr 3 := .times e199 e120
noncomputable def p200 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[36,0],[0,0]],[[0,0],[0,0]],[[278,0],[0,0]],[[0,0],[0,0]],[[1206,0],[0,0]],[[0,0],[0,0]],[[3234,0],[0,0]],[[0,0],[0,0]],[[5560,2],[2,0]],[[0,0],[0,0]],[[6148,18],[18,0]],[[0,0],[0,0]],[[4254,60],[60,0]],[[0,0],[0,0]],[[1712,92],[92,0]],[[0,0],[0,0]],[[336,66],[66,0]],[[0,0],[0,0]],[[18,18],[18,2]],[[0],[0,0]],[[0],[0,2]]]
theorem step200 : p200=NestedArithmetic.mul p199 p120 := by decide +kernel
#print axioms step200
theorem h200 : NestedArithmetic.compile e200=p200 := StagedExprCompile.compile_times e200 e199 e120 p199 p120 p200 rfl h199 h120 step200
#print axioms h200
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
