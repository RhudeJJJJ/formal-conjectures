/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode178
import Proofs.RadenkovicGutmanD30Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-56],[0]],[[0,0],[0]],[[-922,0],[0,0]],[[0,0],[0,0]],[[-6352,0],[0,0]],[[0,0],[0,0]],[[-23726,0],[0,0]],[[0,0],[0,0]],[[-51976,0],[0,0]],[[0,0],[0,0]],[[-67224,-56],[-56,0]],[[0,0],[0,0]],[[-48400,-418],[-418,0]],[[0,0],[0,0]],[[-15662,-1022],[-1022,0]],[[0,0],[0,0]],[[96,-864],[-864,0]],[[0,0],[0,0]],[[846,-114],[-114,0]],[[0,0],[0,0]],[[0,90],[90,-56]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
