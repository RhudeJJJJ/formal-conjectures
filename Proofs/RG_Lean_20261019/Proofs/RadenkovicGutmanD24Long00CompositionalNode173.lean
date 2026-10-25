/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode165
import Proofs.RadenkovicGutmanD24Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-44],[0]],[[0,0],[0]],[[-604,0],[0,0]],[[0,0],[0,0]],[[-3304,0],[0,0]],[[0,0],[0,0]],[[-8876,0],[0,0]],[[0,0],[0,0]],[[-10672,0],[0,0]],[[0,0],[0,0]],[[816,-44],[-44,0]],[[0,0],[0,0]],[[17384,-328],[-328,0]],[[0,0],[0,0]],[[19828,-800],[-800,0]],[[0,0],[0,0]],[[9564,-672],[-672,0]],[[0,0],[0,0]],[[1764,-84],[-84,0]],[[0,0],[0,0]],[[0,72],[72,-44]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
