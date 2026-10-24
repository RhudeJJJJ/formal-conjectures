/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode188
import Proofs.RadenkovicGutmanD2Long00CompositionalNode174
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e199 : NestedArithmetic.Expr 3 := .times e188 e174
noncomputable def p199 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[36,0],[0,0]],[[0,0],[0,0]],[[278,0],[0,0]],[[0,0],[0,0]],[[1206,0],[0,0]],[[0,0],[0,0]],[[3234,0],[0,0]],[[0,0],[0,0]],[[5560,2],[2,0]],[[0,0],[0,0]],[[6148,18],[18,0]],[[0,0],[0,0]],[[4254,60],[60,0]],[[0,0],[0,0]],[[1712,92],[92,0]],[[0,0],[0,0]],[[336,66],[66,0]],[[0,0],[0,0]],[[18,18],[18,2]],[[0],[0,0]],[[0],[0,2]]]
theorem step199 : p199=NestedArithmetic.mul p188 p174 := by decide +kernel
#print axioms step199
theorem h199 : NestedArithmetic.compile e199=p199 := StagedExprCompile.compile_times e199 e188 e174 p188 p174 p199 rfl h188 h174 step199
#print axioms h199
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
