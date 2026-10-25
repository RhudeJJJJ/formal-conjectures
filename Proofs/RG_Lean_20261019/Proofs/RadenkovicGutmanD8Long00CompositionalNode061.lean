/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode059
import Proofs.RadenkovicGutmanD8Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,24],[24,-12]],[[0,0],[0]],[[252,-4],[-4]],[[0,0],[0]],[[492,-160],[-160]],[[0,0],[0]],[[-2132,-208],[-208]],[[0,0],[0]],[[-8712,-88],[-88]],[[0,0],[0]],[[-13104,-12],[-12]],[[0]],[[-10528]],[[0]],[[-4916]],[[0]],[[-1336]],[[0]],[[-196]],[[0]],[[-12]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
