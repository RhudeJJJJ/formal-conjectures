/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode165
import Proofs.RadenkovicGutmanD18Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-32],[0]],[[0,0],[0]],[[-436,0],[0,0]],[[0,0],[0,0]],[[-2356,0],[0,0]],[[0,0],[0,0]],[[-6176,0],[0,0]],[[0,0],[0,0]],[[-6868,0],[0,0]],[[0,0],[0,0]],[[2256,-32],[-32,0]],[[0,0],[0,0]],[[14468,-238],[-238,0]],[[0,0],[0,0]],[[15568,-578],[-578,0]],[[0,0],[0,0]],[[7332,-480],[-480,0]],[[0,0],[0,0]],[[1332,-54],[-54,0]],[[0,0],[0,0]],[[0,54],[54,-32]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
