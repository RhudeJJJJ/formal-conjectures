/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode059
import Proofs.RadenkovicGutmanD34Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,102],[102,-64]],[[0,0],[0]],[[954,-134],[-134]],[[0,0],[0]],[[24,-992],[-992]],[[0,0],[0]],[[-18122,-1170],[-1170]],[[0,0],[0]],[[-55616,-478],[-478]],[[0,0],[0]],[[-77064,-64],[-64]],[[0]],[[-59512]],[[0]],[[-27146]],[[0]],[[-7264]],[[0]],[[-1054]],[[0]],[[-64]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
