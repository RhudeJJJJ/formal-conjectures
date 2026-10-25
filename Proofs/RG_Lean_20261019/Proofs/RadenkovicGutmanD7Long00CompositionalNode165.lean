/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode164
import Proofs.RadenkovicGutmanD7Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-10],[0]],[[0,0],[0]],[[-142,0],[0,0]],[[0,0],[0,0]],[[-828,0],[0,0]],[[0,0],[0,0]],[[-2542,0],[0,0]],[[0,0],[0,0]],[[-4360,0],[0,0]],[[0,0],[0,0]],[[-4008,-10],[-10,0]],[[0,0],[0,0]],[[-1476,-80],[-80,0]],[[0,0],[0,0]],[[450,-220],[-220,0]],[[0,0],[0,0]],[[594,-240],[-240,0]],[[0,0],[0,0]],[[162,-90],[-90,0]],[[0],[0,0]],[[0],[0,-10]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
