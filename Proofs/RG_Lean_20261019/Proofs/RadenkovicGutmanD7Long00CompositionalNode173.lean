/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode165
import Proofs.RadenkovicGutmanD7Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-10],[0]],[[0,0],[0]],[[-128,0],[0,0]],[[0,0],[0,0]],[[-618,0],[0,0]],[[0,0],[0,0]],[[-1226,0],[0,0]],[[0,0],[0,0]],[[106,0],[0,0]],[[0,0],[0,0]],[[4896,-10],[-10,0]],[[0,0],[0,0]],[[9122,-73],[-73,0]],[[0,0],[0,0]],[[7758,-171],[-171,0]],[[0,0],[0,0]],[[3240,-128],[-128,0]],[[0,0],[0,0]],[[540,1],[1,0]],[[0,0],[0,0]],[[0,21],[21,-10]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
