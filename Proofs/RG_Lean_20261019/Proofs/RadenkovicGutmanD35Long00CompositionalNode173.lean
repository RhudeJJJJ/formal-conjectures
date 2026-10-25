/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode165
import Proofs.RadenkovicGutmanD35Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-66],[0]],[[0,0],[0]],[[-912,0],[0,0]],[[0,0],[0,0]],[[-5042,0],[0,0]],[[0,0],[0,0]],[[-13826,0],[0,0]],[[0,0],[0,0]],[[-17646,0],[0,0]],[[0,0],[0,0]],[[-1824,-66],[-66,0]],[[0,0],[0,0]],[[22730,-493],[-493,0]],[[0,0],[0,0]],[[27638,-1207],[-1207,0]],[[0,0],[0,0]],[[13656,-1024],[-1024,0]],[[0,0],[0,0]],[[2556,-139],[-139,0]],[[0,0],[0,0]],[[0,105],[105,-66]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
