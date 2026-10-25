/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode059
import Proofs.RadenkovicGutmanD10Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,30],[30,-16]],[[0,0],[0]],[[306,-14],[-14]],[[0,0],[0]],[[456,-224],[-224]],[[0,0],[0]],[[-3362,-282],[-282]],[[0,0],[0]],[[-12320,-118],[-118]],[[0,0],[0]],[[-18024,-16],[-16]],[[0]],[[-14296]],[[0]],[[-6626]],[[0]],[[-1792]],[[0]],[[-262]],[[0]],[[-16]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
