/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode059
import Proofs.RadenkovicGutmanD16Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,48],[48,-28]],[[0,0],[0]],[[468,-44],[-44]],[[0,0],[0]],[[348,-416],[-416]],[[0,0],[0]],[[-7052,-504],[-504]],[[0,0],[0]],[[-23144,-208],[-208]],[[0,0],[0]],[[-32784,-28],[-28]],[[0]],[[-25600]],[[0]],[[-11756]],[[0]],[[-3160]],[[0]],[[-460]],[[0]],[[-28]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
