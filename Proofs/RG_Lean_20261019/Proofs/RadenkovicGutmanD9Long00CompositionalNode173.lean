/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode165
import Proofs.RadenkovicGutmanD9Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-14],[0]],[[0,0],[0]],[[-184,0],[0,0]],[[0,0],[0,0]],[[-934,0],[0,0]],[[0,0],[0,0]],[[-2126,0],[0,0]],[[0,0],[0,0]],[[-1162,0],[0,0]],[[0,0],[0,0]],[[4416,-14],[-14,0]],[[0,0],[0,0]],[[10094,-103],[-103,0]],[[0,0],[0,0]],[[9178,-245],[-245,0]],[[0,0],[0,0]],[[3984,-192],[-192,0]],[[0,0],[0,0]],[[684,-9],[-9,0]],[[0,0],[0,0]],[[0,27],[27,-14]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
