/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode165
import Proofs.RadenkovicGutmanD32Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-60],[0]],[[0,0],[0]],[[-828,0],[0,0]],[[0,0],[0,0]],[[-4568,0],[0,0]],[[0,0],[0,0]],[[-12476,0],[0,0]],[[0,0],[0,0]],[[-15744,0],[0,0]],[[0,0],[0,0]],[[-1104,-60],[-60,0]],[[0,0],[0,0]],[[21272,-448],[-448,0]],[[0,0],[0,0]],[[25508,-1096],[-1096,0]],[[0,0],[0,0]],[[12540,-928],[-928,0]],[[0,0],[0,0]],[[2340,-124],[-124,0]],[[0,0],[0,0]],[[0,96],[96,-60]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
