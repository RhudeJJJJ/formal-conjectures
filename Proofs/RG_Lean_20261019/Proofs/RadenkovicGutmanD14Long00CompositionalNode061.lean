/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode059
import Proofs.RadenkovicGutmanD14Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,42],[42,-24]],[[0,0],[0]],[[414,-34],[-34]],[[0,0],[0]],[[384,-352],[-352]],[[0,0],[0]],[[-5822,-430],[-430]],[[0,0],[0]],[[-19536,-178],[-178]],[[0,0],[0]],[[-27864,-24],[-24]],[[0]],[[-21832]],[[0]],[[-10046]],[[0]],[[-2704]],[[0]],[[-394]],[[0]],[[-24]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
