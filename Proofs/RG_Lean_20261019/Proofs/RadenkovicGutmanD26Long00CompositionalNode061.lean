/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode059
import Proofs.RadenkovicGutmanD26Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,78],[78,-48]],[[0,0],[0]],[[738,-94],[-94]],[[0,0],[0]],[[168,-736],[-736]],[[0,0],[0]],[[-13202,-874],[-874]],[[0,0],[0]],[[-41184,-358],[-358]],[[0,0],[0]],[[-57384,-48],[-48]],[[0]],[[-44440]],[[0]],[[-20306]],[[0]],[[-5440]],[[0]],[[-790]],[[0]],[[-48]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
