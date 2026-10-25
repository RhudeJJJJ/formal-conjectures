/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode174
import Proofs.RadenkovicGutmanD21Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-38],[0]],[[0,0],[0]],[[-646,0],[0,0]],[[0,0],[0,0]],[[-4636,0],[0,0]],[[0,0],[0,0]],[[-18278,0],[0,0]],[[0,0],[0,0]],[[-43168,0],[0,0]],[[0,0],[0,0]],[[-62472,-38],[-38,0]],[[0,0],[0,0]],[[-54340,-304],[-304,0]],[[0,0],[0,0]],[[-26486,-836],[-836,0]],[[0,0],[0,0]],[[-6042,-912],[-912,0]],[[0,0],[0,0]],[[-342,-342],[-342,0]],[[0],[0,0]],[[0],[0,-38]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
