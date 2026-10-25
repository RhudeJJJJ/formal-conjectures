/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode165
import Proofs.RadenkovicGutmanD33Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-62],[0]],[[0,0],[0]],[[-856,0],[0,0]],[[0,0],[0,0]],[[-4726,0],[0,0]],[[0,0],[0,0]],[[-12926,0],[0,0]],[[0,0],[0,0]],[[-16378,0],[0,0]],[[0,0],[0,0]],[[-1344,-62],[-62,0]],[[0,0],[0,0]],[[21758,-463],[-463,0]],[[0,0],[0,0]],[[26218,-1133],[-1133,0]],[[0,0],[0,0]],[[12912,-960],[-960,0]],[[0,0],[0,0]],[[2412,-129],[-129,0]],[[0,0],[0,0]],[[0,99],[99,-62]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
