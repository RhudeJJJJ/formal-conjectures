/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode178
import Proofs.RadenkovicGutmanD33Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-62],[0]],[[0,0],[0]],[[-1021,0],[0,0]],[[0,0],[0,0]],[[-7036,0],[0,0]],[[0,0],[0,0]],[[-26291,0],[0,0]],[[0,0],[0,0]],[[-57628,0],[0,0]],[[0,0],[0,0]],[[-74604,-62],[-62,0]],[[0,0],[0,0]],[[-53812,-463],[-463,0]],[[0,0],[0,0]],[[-17507,-1133],[-1133,0]],[[0,0],[0,0]],[[42,-960],[-960,0]],[[0,0],[0,0]],[[927,-129],[-129,0]],[[0,0],[0,0]],[[0,99],[99,-62]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
