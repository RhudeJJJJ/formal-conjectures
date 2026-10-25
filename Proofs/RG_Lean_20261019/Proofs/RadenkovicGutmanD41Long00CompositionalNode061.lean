/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode059
import Proofs.RadenkovicGutmanD41Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,123],[123,-78]],[[0,0],[0]],[[1143,-169],[-169]],[[0,0],[0]],[[-102,-1216],[-1216]],[[0,0],[0]],[[-22427,-1429],[-1429]],[[0,0],[0]],[[-68244,-583],[-583]],[[0,0],[0]],[[-94284,-78],[-78]],[[0]],[[-72700]],[[0]],[[-33131]],[[0]],[[-8860]],[[0]],[[-1285]],[[0]],[[-78]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
