/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode177
import Proofs.RadenkovicGutmanD5Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-6],[0]],[[0,0],[0]],[[-102,0],[0,0]],[[0,0],[0,0]],[[-732,0],[0,0]],[[0,0],[0,0]],[[-2886,0],[0,0]],[[0,0],[0,0]],[[-6816,0],[0,0]],[[0,0],[0,0]],[[-9864,-6],[-6,0]],[[0,0],[0,0]],[[-8580,-48],[-48,0]],[[0,0],[0,0]],[[-4182,-132],[-132,0]],[[0,0],[0,0]],[[-954,-144],[-144,0]],[[0,0],[0,0]],[[-54,-54],[-54,0]],[[0],[0,0]],[[0],[0,-6]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
