/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode177
import Proofs.RadenkovicGutmanD26Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-48],[0]],[[0,0],[0]],[[-816,0],[0,0]],[[0,0],[0,0]],[[-5856,0],[0,0]],[[0,0],[0,0]],[[-23088,0],[0,0]],[[0,0],[0,0]],[[-54528,0],[0,0]],[[0,0],[0,0]],[[-78912,-48],[-48,0]],[[0,0],[0,0]],[[-68640,-384],[-384,0]],[[0,0],[0,0]],[[-33456,-1056],[-1056,0]],[[0,0],[0,0]],[[-7632,-1152],[-1152,0]],[[0,0],[0,0]],[[-432,-432],[-432,0]],[[0],[0,0]],[[0],[0,-48]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
