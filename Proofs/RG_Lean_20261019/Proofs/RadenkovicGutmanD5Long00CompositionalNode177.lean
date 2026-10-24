/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode174
import Proofs.RadenkovicGutmanD5Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-6],[0]],[[0,0],[0]],[[-102,0],[0,0]],[[0,0],[0,0]],[[-732,0],[0,0]],[[0,0],[0,0]],[[-2886,0],[0,0]],[[0,0],[0,0]],[[-6816,0],[0,0]],[[0,0],[0,0]],[[-9864,-6],[-6,0]],[[0,0],[0,0]],[[-8580,-48],[-48,0]],[[0,0],[0,0]],[[-4182,-132],[-132,0]],[[0,0],[0,0]],[[-954,-144],[-144,0]],[[0,0],[0,0]],[[-54,-54],[-54,0]],[[0],[0,0]],[[0],[0,-6]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
