/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode178
import Proofs.RadenkovicGutmanD17Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-30],[0]],[[0,0],[0]],[[-493,0],[0,0]],[[0,0],[0,0]],[[-3388,0],[0,0]],[[0,0],[0,0]],[[-12611,0],[0,0]],[[0,0],[0,0]],[[-27484,0],[0,0]],[[0,0],[0,0]],[[-35244,-30],[-30,0]],[[0,0],[0,0]],[[-24948,-223],[-223,0]],[[0,0],[0,0]],[[-7667,-541],[-541,0]],[[0,0],[0,0]],[[330,-448],[-448,0]],[[0,0],[0,0]],[[495,-49],[-49,0]],[[0,0],[0,0]],[[0,51],[51,-30]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
