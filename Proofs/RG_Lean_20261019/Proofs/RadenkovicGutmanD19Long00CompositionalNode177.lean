/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode174
import Proofs.RadenkovicGutmanD19Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-34],[0]],[[0,0],[0]],[[-578,0],[0,0]],[[0,0],[0,0]],[[-4148,0],[0,0]],[[0,0],[0,0]],[[-16354,0],[0,0]],[[0,0],[0,0]],[[-38624,0],[0,0]],[[0,0],[0,0]],[[-55896,-34],[-34,0]],[[0,0],[0,0]],[[-48620,-272],[-272,0]],[[0,0],[0,0]],[[-23698,-748],[-748,0]],[[0,0],[0,0]],[[-5406,-816],[-816,0]],[[0,0],[0,0]],[[-306,-306],[-306,0]],[[0],[0,0]],[[0],[0,-34]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
