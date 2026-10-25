/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode159
import Proofs.RadenkovicGutmanD10Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-8],[0]],[[0,0],[0]],[[-120,0],[0,0]],[[0,0],[0,0]],[[-752,0],[0,0]],[[0,0],[0,0]],[[-2552,0],[0,0]],[[0,0],[0,0]],[[-5088,0],[0,0]],[[0,0],[0,0]],[[-6048,-8],[-8,0]],[[0,0],[0,0]],[[-4112,-64],[-64,0]],[[0,0],[0,0]],[[-1336,-176],[-176,0]],[[0,0],[0,0]],[[-24,-192],[-192,0]],[[0,0],[0,0]],[[72,-72],[-72,0]],[[0],[0,0]],[[0],[0,-8]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
