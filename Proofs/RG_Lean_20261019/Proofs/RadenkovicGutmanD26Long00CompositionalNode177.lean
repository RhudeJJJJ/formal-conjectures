/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode174
import Proofs.RadenkovicGutmanD26Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-48],[0]],[[0,0],[0]],[[-816,0],[0,0]],[[0,0],[0,0]],[[-5856,0],[0,0]],[[0,0],[0,0]],[[-23088,0],[0,0]],[[0,0],[0,0]],[[-54528,0],[0,0]],[[0,0],[0,0]],[[-78912,-48],[-48,0]],[[0,0],[0,0]],[[-68640,-384],[-384,0]],[[0,0],[0,0]],[[-33456,-1056],[-1056,0]],[[0,0],[0,0]],[[-7632,-1152],[-1152,0]],[[0,0],[0,0]],[[-432,-432],[-432,0]],[[0],[0,0]],[[0],[0,-48]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
