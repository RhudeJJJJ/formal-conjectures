/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode059
import Proofs.RadenkovicGutmanD5Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,15],[15,-6]],[[0,0],[0]],[[171,11],[11]],[[0,0],[0]],[[546,-64],[-64]],[[0,0],[0]],[[-287,-97],[-97]],[[0,0],[0]],[[-3300,-43],[-43]],[[0,0],[0]],[[-5724,-6],[-6]],[[0]],[[-4876]],[[0]],[[-2351]],[[0]],[[-652]],[[0]],[[-97]],[[0]],[[-6]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
