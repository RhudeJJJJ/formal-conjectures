/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode059
import Proofs.RadenkovicGutmanD30Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,90],[90,-56]],[[0,0],[0]],[[846,-114],[-114]],[[0,0],[0]],[[96,-864],[-864]],[[0,0],[0]],[[-15662,-1022],[-1022]],[[0,0],[0]],[[-48400,-418],[-418]],[[0,0],[0]],[[-67224,-56],[-56]],[[0]],[[-51976]],[[0]],[[-23726]],[[0]],[[-6352]],[[0]],[[-922]],[[0]],[[-56]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
