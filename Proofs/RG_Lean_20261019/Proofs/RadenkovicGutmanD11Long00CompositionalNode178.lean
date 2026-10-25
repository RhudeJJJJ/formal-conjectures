/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode177
import Proofs.RadenkovicGutmanD11Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-18],[0]],[[0,0],[0]],[[-306,0],[0,0]],[[0,0],[0,0]],[[-2196,0],[0,0]],[[0,0],[0,0]],[[-8658,0],[0,0]],[[0,0],[0,0]],[[-20448,0],[0,0]],[[0,0],[0,0]],[[-29592,-18],[-18,0]],[[0,0],[0,0]],[[-25740,-144],[-144,0]],[[0,0],[0,0]],[[-12546,-396],[-396,0]],[[0,0],[0,0]],[[-2862,-432],[-432,0]],[[0,0],[0,0]],[[-162,-162],[-162,0]],[[0],[0,0]],[[0],[0,-18]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
