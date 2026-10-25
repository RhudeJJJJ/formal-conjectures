/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode059
import Proofs.RadenkovicGutmanD21Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,63],[63,-38]],[[0,0],[0]],[[603,-69],[-69]],[[0,0],[0]],[[258,-576],[-576]],[[0,0],[0]],[[-10127,-689],[-689]],[[0,0],[0]],[[-32164,-283],[-283]],[[0,0],[0]],[[-45084,-38],[-38]],[[0]],[[-35020]],[[0]],[[-16031]],[[0]],[[-4300]],[[0]],[[-625]],[[0]],[[-38]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
