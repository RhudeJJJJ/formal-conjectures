/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode165
import Proofs.RadenkovicGutmanD16Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-28],[0]],[[0,0],[0]],[[-380,0],[0,0]],[[0,0],[0,0]],[[-2040,0],[0,0]],[[0,0],[0,0]],[[-5276,0],[0,0]],[[0,0],[0,0]],[[-5600,0],[0,0]],[[0,0],[0,0]],[[2736,-28],[-28,0]],[[0,0],[0,0]],[[13496,-208],[-208,0]],[[0,0],[0,0]],[[14148,-504],[-504,0]],[[0,0],[0,0]],[[6588,-416],[-416,0]],[[0,0],[0,0]],[[1188,-44],[-44,0]],[[0,0],[0,0]],[[0,48],[48,-28]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
