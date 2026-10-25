/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode177
import Proofs.RadenkovicGutmanD21Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-38],[0]],[[0,0],[0]],[[-646,0],[0,0]],[[0,0],[0,0]],[[-4636,0],[0,0]],[[0,0],[0,0]],[[-18278,0],[0,0]],[[0,0],[0,0]],[[-43168,0],[0,0]],[[0,0],[0,0]],[[-62472,-38],[-38,0]],[[0,0],[0,0]],[[-54340,-304],[-304,0]],[[0,0],[0,0]],[[-26486,-836],[-836,0]],[[0,0],[0,0]],[[-6042,-912],[-912,0]],[[0,0],[0,0]],[[-342,-342],[-342,0]],[[0],[0,0]],[[0],[0,-38]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
