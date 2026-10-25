/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode165
import Proofs.RadenkovicGutmanD34Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-64],[0]],[[0,0],[0]],[[-884,0],[0,0]],[[0,0],[0,0]],[[-4884,0],[0,0]],[[0,0],[0,0]],[[-13376,0],[0,0]],[[0,0],[0,0]],[[-17012,0],[0,0]],[[0,0],[0,0]],[[-1584,-64],[-64,0]],[[0,0],[0,0]],[[22244,-478],[-478,0]],[[0,0],[0,0]],[[26928,-1170],[-1170,0]],[[0,0],[0,0]],[[13284,-992],[-992,0]],[[0,0],[0,0]],[[2484,-134],[-134,0]],[[0,0],[0,0]],[[0,102],[102,-64]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
