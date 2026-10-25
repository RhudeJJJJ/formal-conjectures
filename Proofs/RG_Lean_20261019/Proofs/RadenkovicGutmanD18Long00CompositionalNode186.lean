/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode178
import Proofs.RadenkovicGutmanD18Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-32],[0]],[[0,0],[0]],[[-526,0],[0,0]],[[0,0],[0,0]],[[-3616,0],[0,0]],[[0,0],[0,0]],[[-13466,0],[0,0]],[[0,0],[0,0]],[[-29368,0],[0,0]],[[0,0],[0,0]],[[-37704,-32],[-32,0]],[[0,0],[0,0]],[[-26752,-238],[-238,0]],[[0,0],[0,0]],[[-8282,-578],[-578,0]],[[0,0],[0,0]],[[312,-480],[-480,0]],[[0,0],[0,0]],[[522,-54],[-54,0]],[[0,0],[0,0]],[[0,54],[54,-32]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
