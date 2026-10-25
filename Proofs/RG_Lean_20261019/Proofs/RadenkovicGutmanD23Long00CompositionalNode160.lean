/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode159
import Proofs.RadenkovicGutmanD23Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-21],[0]],[[0,0],[0]],[[-315,0],[0,0]],[[0,0],[0,0]],[[-1974,0],[0,0]],[[0,0],[0,0]],[[-6699,0],[0,0]],[[0,0],[0,0]],[[-13356,0],[0,0]],[[0,0],[0,0]],[[-15876,-21],[-21,0]],[[0,0],[0,0]],[[-10794,-168],[-168,0]],[[0,0],[0,0]],[[-3507,-462],[-462,0]],[[0,0],[0,0]],[[-63,-504],[-504,0]],[[0,0],[0,0]],[[189,-189],[-189,0]],[[0],[0,0]],[[0],[0,-21]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
