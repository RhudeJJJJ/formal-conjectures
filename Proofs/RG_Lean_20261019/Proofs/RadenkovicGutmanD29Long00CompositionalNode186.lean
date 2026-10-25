/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode178
import Proofs.RadenkovicGutmanD29Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-54],[0]],[[0,0],[0]],[[-889,0],[0,0]],[[0,0],[0,0]],[[-6124,0],[0,0]],[[0,0],[0,0]],[[-22871,0],[0,0]],[[0,0],[0,0]],[[-50092,0],[0,0]],[[0,0],[0,0]],[[-64764,-54],[-54,0]],[[0,0],[0,0]],[[-46596,-403],[-403,0]],[[0,0],[0,0]],[[-15047,-985],[-985,0]],[[0,0],[0,0]],[[114,-832],[-832,0]],[[0,0],[0,0]],[[819,-109],[-109,0]],[[0,0],[0,0]],[[0,87],[87,-54]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
