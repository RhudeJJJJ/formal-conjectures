/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode178
import Proofs.RadenkovicGutmanD8Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-12],[0]],[[0,0],[0]],[[-196,0],[0,0]],[[0,0],[0,0]],[[-1336,0],[0,0]],[[0,0],[0,0]],[[-4916,0],[0,0]],[[0,0],[0,0]],[[-10528,0],[0,0]],[[0,0],[0,0]],[[-13104,-12],[-12,0]],[[0,0],[0,0]],[[-8712,-88],[-88,0]],[[0,0],[0,0]],[[-2132,-208],[-208,0]],[[0,0],[0,0]],[[492,-160],[-160,0]],[[0,0],[0,0]],[[252,-4],[-4,0]],[[0,0],[0,0]],[[0,24],[24,-12]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
