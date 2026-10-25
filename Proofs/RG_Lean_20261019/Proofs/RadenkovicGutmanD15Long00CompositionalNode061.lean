/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode059
import Proofs.RadenkovicGutmanD15Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,45],[45,-26]],[[0,0],[0]],[[441,-39],[-39]],[[0,0],[0]],[[366,-384],[-384]],[[0,0],[0]],[[-6437,-467],[-467]],[[0,0],[0]],[[-21340,-193],[-193]],[[0,0],[0]],[[-30324,-26],[-26]],[[0]],[[-23716]],[[0]],[[-10901]],[[0]],[[-2932]],[[0]],[[-427]],[[0]],[[-26]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
