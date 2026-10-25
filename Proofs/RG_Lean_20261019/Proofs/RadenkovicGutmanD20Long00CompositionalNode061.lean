/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode059
import Proofs.RadenkovicGutmanD20Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,60],[60,-36]],[[0,0],[0]],[[576,-64],[-64]],[[0,0],[0]],[[276,-544],[-544]],[[0,0],[0]],[[-9512,-652],[-652]],[[0,0],[0]],[[-30360,-268],[-268]],[[0,0],[0]],[[-42624,-36],[-36]],[[0]],[[-33136]],[[0]],[[-15176]],[[0]],[[-4072]],[[0]],[[-592]],[[0]],[[-36]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
