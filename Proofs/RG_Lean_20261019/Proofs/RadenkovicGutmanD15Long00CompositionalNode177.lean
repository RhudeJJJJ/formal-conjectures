/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode174
import Proofs.RadenkovicGutmanD15Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-26],[0]],[[0,0],[0]],[[-442,0],[0,0]],[[0,0],[0,0]],[[-3172,0],[0,0]],[[0,0],[0,0]],[[-12506,0],[0,0]],[[0,0],[0,0]],[[-29536,0],[0,0]],[[0,0],[0,0]],[[-42744,-26],[-26,0]],[[0,0],[0,0]],[[-37180,-208],[-208,0]],[[0,0],[0,0]],[[-18122,-572],[-572,0]],[[0,0],[0,0]],[[-4134,-624],[-624,0]],[[0,0],[0,0]],[[-234,-234],[-234,0]],[[0],[0,0]],[[0],[0,-26]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
