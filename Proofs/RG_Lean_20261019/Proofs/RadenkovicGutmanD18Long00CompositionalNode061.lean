/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode059
import Proofs.RadenkovicGutmanD18Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,54],[54,-32]],[[0,0],[0]],[[522,-54],[-54]],[[0,0],[0]],[[312,-480],[-480]],[[0,0],[0]],[[-8282,-578],[-578]],[[0,0],[0]],[[-26752,-238],[-238]],[[0,0],[0]],[[-37704,-32],[-32]],[[0]],[[-29368]],[[0]],[[-13466]],[[0]],[[-3616]],[[0]],[[-526]],[[0]],[[-32]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
