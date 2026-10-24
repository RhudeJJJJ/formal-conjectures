/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode164
import Proofs.RadenkovicGutmanD5Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-6],[0]],[[0,0],[0]],[[-82,0],[0,0]],[[0,0],[0,0]],[[-452,0],[0,0]],[[0,0],[0,0]],[[-1266,0],[0,0]],[[0,0],[0,0]],[[-1816,0],[0,0]],[[0,0],[0,0]],[[-984,-6],[-6,0]],[[0,0],[0,0]],[[580,-48],[-48,0]],[[0,0],[0,0]],[[1118,-132],[-132,0]],[[0,0],[0,0]],[[606,-144],[-144,0]],[[0,0],[0,0]],[[126,-54],[-54,0]],[[0],[0,0]],[[0],[0,-6]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
