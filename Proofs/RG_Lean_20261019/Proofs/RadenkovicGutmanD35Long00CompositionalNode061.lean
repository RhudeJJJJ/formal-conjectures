/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode059
import Proofs.RadenkovicGutmanD35Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,105],[105,-66]],[[0,0],[0]],[[981,-139],[-139]],[[0,0],[0]],[[6,-1024],[-1024]],[[0,0],[0]],[[-18737,-1207],[-1207]],[[0,0],[0]],[[-57420,-493],[-493]],[[0,0],[0]],[[-79524,-66],[-66]],[[0]],[[-61396]],[[0]],[[-28001]],[[0]],[[-7492]],[[0]],[[-1087]],[[0]],[[-66]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
