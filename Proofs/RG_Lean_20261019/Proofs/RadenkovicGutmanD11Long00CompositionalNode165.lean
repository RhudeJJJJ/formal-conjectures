/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode164
import Proofs.RadenkovicGutmanD11Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-18],[0]],[[0,0],[0]],[[-262,0],[0,0]],[[0,0],[0,0]],[[-1580,0],[0,0]],[[0,0],[0,0]],[[-5094,0],[0,0]],[[0,0],[0,0]],[[-9448,0],[0,0]],[[0,0],[0,0]],[[-10056,-18],[-18,0]],[[0,0],[0,0]],[[-5588,-144],[-144,0]],[[0,0],[0,0]],[[-886,-396],[-396,0]],[[0,0],[0,0]],[[570,-432],[-432,0]],[[0,0],[0,0]],[[234,-162],[-162,0]],[[0],[0,0]],[[0],[0,-18]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
