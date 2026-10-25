/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode059
import Proofs.RadenkovicGutmanD12Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,36],[36,-20]],[[0,0],[0]],[[360,-24],[-24]],[[0,0],[0]],[[420,-288],[-288]],[[0,0],[0]],[[-4592,-356],[-356]],[[0,0],[0]],[[-15928,-148],[-148]],[[0,0],[0]],[[-22944,-20],[-20]],[[0]],[[-18064]],[[0]],[[-8336]],[[0]],[[-2248]],[[0]],[[-328]],[[0]],[[-20]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
