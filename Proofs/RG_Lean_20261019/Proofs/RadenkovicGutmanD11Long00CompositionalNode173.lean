/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode165
import Proofs.RadenkovicGutmanD11Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-18],[0]],[[0,0],[0]],[[-240,0],[0,0]],[[0,0],[0,0]],[[-1250,0],[0,0]],[[0,0],[0,0]],[[-3026,0],[0,0]],[[0,0],[0,0]],[[-2430,0],[0,0]],[[0,0],[0,0]],[[3936,-18],[-18,0]],[[0,0],[0,0]],[[11066,-133],[-133,0]],[[0,0],[0,0]],[[10598,-319],[-319,0]],[[0,0],[0,0]],[[4728,-256],[-256,0]],[[0,0],[0,0]],[[828,-19],[-19,0]],[[0,0],[0,0]],[[0,33],[33,-18]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
