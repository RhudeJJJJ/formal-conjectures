/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode059
import Proofs.RadenkovicGutmanD31Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,93],[93,-58]],[[0,0],[0]],[[873,-119],[-119]],[[0,0],[0]],[[78,-896],[-896]],[[0,0],[0]],[[-16277,-1059],[-1059]],[[0,0],[0]],[[-50204,-433],[-433]],[[0,0],[0]],[[-69684,-58],[-58]],[[0]],[[-53860]],[[0]],[[-24581]],[[0]],[[-6580]],[[0]],[[-955]],[[0]],[[-58]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
