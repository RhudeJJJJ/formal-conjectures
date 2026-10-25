/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode177
import Proofs.RadenkovicGutmanD15Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-26],[0]],[[0,0],[0]],[[-442,0],[0,0]],[[0,0],[0,0]],[[-3172,0],[0,0]],[[0,0],[0,0]],[[-12506,0],[0,0]],[[0,0],[0,0]],[[-29536,0],[0,0]],[[0,0],[0,0]],[[-42744,-26],[-26,0]],[[0,0],[0,0]],[[-37180,-208],[-208,0]],[[0,0],[0,0]],[[-18122,-572],[-572,0]],[[0,0],[0,0]],[[-4134,-624],[-624,0]],[[0,0],[0,0]],[[-234,-234],[-234,0]],[[0],[0,0]],[[0],[0,-26]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
