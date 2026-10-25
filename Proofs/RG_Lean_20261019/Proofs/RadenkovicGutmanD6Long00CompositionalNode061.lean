/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode059
import Proofs.RadenkovicGutmanD6Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,18],[18,-8]],[[0,0],[0]],[[198,6],[6]],[[0,0],[0]],[[528,-96],[-96]],[[0,0],[0]],[[-902,-134],[-134]],[[0,0],[0]],[[-5104,-58],[-58]],[[0,0],[0]],[[-8184,-8],[-8]],[[0]],[[-6760]],[[0]],[[-3206]],[[0]],[[-880]],[[0]],[[-130]],[[0]],[[-8]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
