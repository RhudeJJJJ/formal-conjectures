/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode119
import Proofs.RadenkovicGutmanD5Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-6],[0]],[[0,0],[0]],[[-82,0],[0,0]],[[0,0],[0,0]],[[-452,0],[0,0]],[[0,0],[0,0]],[[-1266,0],[0,0]],[[0,0],[0,0]],[[-1816,0],[0,0]],[[0,0],[0,0]],[[-984,-6],[-6,0]],[[0,0],[0,0]],[[580,-48],[-48,0]],[[0,0],[0,0]],[[1118,-132],[-132,0]],[[0,0],[0,0]],[[606,-144],[-144,0]],[[0,0],[0,0]],[[126,-54],[-54,0]],[[0],[0,0]],[[0],[0,-6]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
