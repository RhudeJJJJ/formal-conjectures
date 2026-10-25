/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode174
import Proofs.RadenkovicGutmanD11Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-18],[0]],[[0,0],[0]],[[-306,0],[0,0]],[[0,0],[0,0]],[[-2196,0],[0,0]],[[0,0],[0,0]],[[-8658,0],[0,0]],[[0,0],[0,0]],[[-20448,0],[0,0]],[[0,0],[0,0]],[[-29592,-18],[-18,0]],[[0,0],[0,0]],[[-25740,-144],[-144,0]],[[0,0],[0,0]],[[-12546,-396],[-396,0]],[[0,0],[0,0]],[[-2862,-432],[-432,0]],[[0,0],[0,0]],[[-162,-162],[-162,0]],[[0],[0,0]],[[0],[0,-18]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
