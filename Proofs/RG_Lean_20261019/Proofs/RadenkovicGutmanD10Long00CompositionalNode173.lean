/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode165
import Proofs.RadenkovicGutmanD10Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-16],[0]],[[0,0],[0]],[[-212,0],[0,0]],[[0,0],[0,0]],[[-1092,0],[0,0]],[[0,0],[0,0]],[[-2576,0],[0,0]],[[0,0],[0,0]],[[-1796,0],[0,0]],[[0,0],[0,0]],[[4176,-16],[-16,0]],[[0,0],[0,0]],[[10580,-118],[-118,0]],[[0,0],[0,0]],[[9888,-282],[-282,0]],[[0,0],[0,0]],[[4356,-224],[-224,0]],[[0,0],[0,0]],[[756,-14],[-14,0]],[[0,0],[0,0]],[[0,30],[30,-16]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
