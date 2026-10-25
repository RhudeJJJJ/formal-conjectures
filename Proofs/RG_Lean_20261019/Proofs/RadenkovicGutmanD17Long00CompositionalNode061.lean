/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode059
import Proofs.RadenkovicGutmanD17Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,51],[51,-30]],[[0,0],[0]],[[495,-49],[-49]],[[0,0],[0]],[[330,-448],[-448]],[[0,0],[0]],[[-7667,-541],[-541]],[[0,0],[0]],[[-24948,-223],[-223]],[[0,0],[0]],[[-35244,-30],[-30]],[[0]],[[-27484]],[[0]],[[-12611]],[[0]],[[-3388]],[[0]],[[-493]],[[0]],[[-30]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
