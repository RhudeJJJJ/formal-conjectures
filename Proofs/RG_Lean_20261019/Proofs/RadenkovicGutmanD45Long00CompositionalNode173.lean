/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode165
import Proofs.RadenkovicGutmanD45Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-86],[0]],[[0,0],[0]],[[-1192,0],[0,0]],[[0,0],[0,0]],[[-6622,0],[0,0]],[[0,0],[0,0]],[[-18326,0],[0,0]],[[0,0],[0,0]],[[-23986,0],[0,0]],[[0,0],[0,0]],[[-4224,-86],[-86,0]],[[0,0],[0,0]],[[27590,-643],[-643,0]],[[0,0],[0,0]],[[34738,-1577],[-1577,0]],[[0,0],[0,0]],[[17376,-1344],[-1344,0]],[[0,0],[0,0]],[[3276,-189],[-189,0]],[[0,0],[0,0]],[[0,135],[135,-86]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
