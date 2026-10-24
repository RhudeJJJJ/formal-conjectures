/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode165
import Proofs.RadenkovicGutmanD5Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-6],[0]],[[0,0],[0]],[[-72,0],[0,0]],[[0,0],[0,0]],[[-302,0],[0,0]],[[0,0],[0,0]],[[-326,0],[0,0]],[[0,0],[0,0]],[[1374,0],[0,0]],[[0,0],[0,0]],[[5376,-6],[-6,0]],[[0,0],[0,0]],[[8150,-43],[-43,0]],[[0,0],[0,0]],[[6338,-97],[-97,0]],[[0,0],[0,0]],[[2496,-64],[-64,0]],[[0,0],[0,0]],[[396,11],[11,0]],[[0,0],[0,0]],[[0,15],[15,-6]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
