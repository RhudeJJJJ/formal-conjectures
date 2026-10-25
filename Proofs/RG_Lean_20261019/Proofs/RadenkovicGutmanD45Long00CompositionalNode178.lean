/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode177
import Proofs.RadenkovicGutmanD45Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-86],[0]],[[0,0],[0]],[[-1462,0],[0,0]],[[0,0],[0,0]],[[-10492,0],[0,0]],[[0,0],[0,0]],[[-41366,0],[0,0]],[[0,0],[0,0]],[[-97696,0],[0,0]],[[0,0],[0,0]],[[-141384,-86],[-86,0]],[[0,0],[0,0]],[[-122980,-688],[-688,0]],[[0,0],[0,0]],[[-59942,-1892],[-1892,0]],[[0,0],[0,0]],[[-13674,-2064],[-2064,0]],[[0,0],[0,0]],[[-774,-774],[-774,0]],[[0],[0,0]],[[0],[0,-86]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
