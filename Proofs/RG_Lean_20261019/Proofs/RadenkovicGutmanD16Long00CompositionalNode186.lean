/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode178
import Proofs.RadenkovicGutmanD16Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-28],[0]],[[0,0],[0]],[[-460,0],[0,0]],[[0,0],[0,0]],[[-3160,0],[0,0]],[[0,0],[0,0]],[[-11756,0],[0,0]],[[0,0],[0,0]],[[-25600,0],[0,0]],[[0,0],[0,0]],[[-32784,-28],[-28,0]],[[0,0],[0,0]],[[-23144,-208],[-208,0]],[[0,0],[0,0]],[[-7052,-504],[-504,0]],[[0,0],[0,0]],[[348,-416],[-416,0]],[[0,0],[0,0]],[[468,-44],[-44,0]],[[0,0],[0,0]],[[0,48],[48,-28]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
