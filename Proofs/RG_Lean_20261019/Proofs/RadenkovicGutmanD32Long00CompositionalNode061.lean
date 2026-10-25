/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode059
import Proofs.RadenkovicGutmanD32Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,96],[96,-60]],[[0,0],[0]],[[900,-124],[-124]],[[0,0],[0]],[[60,-928],[-928]],[[0,0],[0]],[[-16892,-1096],[-1096]],[[0,0],[0]],[[-52008,-448],[-448]],[[0,0],[0]],[[-72144,-60],[-60]],[[0]],[[-55744]],[[0]],[[-25436]],[[0]],[[-6808]],[[0]],[[-988]],[[0]],[[-60]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
