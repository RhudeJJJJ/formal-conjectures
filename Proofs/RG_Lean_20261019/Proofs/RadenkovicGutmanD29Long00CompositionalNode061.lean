/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode059
import Proofs.RadenkovicGutmanD29Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,87],[87,-54]],[[0,0],[0]],[[819,-109],[-109]],[[0,0],[0]],[[114,-832],[-832]],[[0,0],[0]],[[-15047,-985],[-985]],[[0,0],[0]],[[-46596,-403],[-403]],[[0,0],[0]],[[-64764,-54],[-54]],[[0]],[[-50092]],[[0]],[[-22871]],[[0]],[[-6124]],[[0]],[[-889]],[[0]],[[-54]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
