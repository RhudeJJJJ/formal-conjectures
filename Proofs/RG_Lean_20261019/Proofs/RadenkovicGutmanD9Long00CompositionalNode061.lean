/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode059
import Proofs.RadenkovicGutmanD9Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,27],[27,-14]],[[0,0],[0]],[[279,-9],[-9]],[[0,0],[0]],[[474,-192],[-192]],[[0,0],[0]],[[-2747,-245],[-245]],[[0,0],[0]],[[-10516,-103],[-103]],[[0,0],[0]],[[-15564,-14],[-14]],[[0]],[[-12412]],[[0]],[[-5771]],[[0]],[[-1564]],[[0]],[[-229]],[[0]],[[-14]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
