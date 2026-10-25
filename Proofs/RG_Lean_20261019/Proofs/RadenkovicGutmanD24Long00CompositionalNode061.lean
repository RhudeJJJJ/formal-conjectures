/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode059
import Proofs.RadenkovicGutmanD24Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,72],[72,-44]],[[0,0],[0]],[[684,-84],[-84]],[[0,0],[0]],[[204,-672],[-672]],[[0,0],[0]],[[-11972,-800],[-800]],[[0,0],[0]],[[-37576,-328],[-328]],[[0,0],[0]],[[-52464,-44],[-44]],[[0]],[[-40672]],[[0]],[[-18596]],[[0]],[[-4984]],[[0]],[[-724]],[[0]],[[-44]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
