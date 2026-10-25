/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode174
import Proofs.RadenkovicGutmanD45Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-86],[0]],[[0,0],[0]],[[-1462,0],[0,0]],[[0,0],[0,0]],[[-10492,0],[0,0]],[[0,0],[0,0]],[[-41366,0],[0,0]],[[0,0],[0,0]],[[-97696,0],[0,0]],[[0,0],[0,0]],[[-141384,-86],[-86,0]],[[0,0],[0,0]],[[-122980,-688],[-688,0]],[[0,0],[0,0]],[[-59942,-1892],[-1892,0]],[[0,0],[0,0]],[[-13674,-2064],[-2064,0]],[[0,0],[0,0]],[[-774,-774],[-774,0]],[[0],[0,0]],[[0],[0,-86]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
