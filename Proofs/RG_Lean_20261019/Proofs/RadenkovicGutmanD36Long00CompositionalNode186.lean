/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode178
import Proofs.RadenkovicGutmanD36Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-68],[0]],[[0,0],[0]],[[-1120,0],[0,0]],[[0,0],[0,0]],[[-7720,0],[0,0]],[[0,0],[0,0]],[[-28856,0],[0,0]],[[0,0],[0,0]],[[-63280,0],[0,0]],[[0,0],[0,0]],[[-81984,-68],[-68,0]],[[0,0],[0,0]],[[-59224,-508],[-508,0]],[[0,0],[0,0]],[[-19352,-1244],[-1244,0]],[[0,0],[0,0]],[[-12,-1056],[-1056,0]],[[0,0],[0,0]],[[1008,-144],[-144,0]],[[0,0],[0,0]],[[0,108],[108,-68]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
