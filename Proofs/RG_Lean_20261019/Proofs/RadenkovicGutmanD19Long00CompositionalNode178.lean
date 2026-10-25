/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode177
import Proofs.RadenkovicGutmanD19Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-34],[0]],[[0,0],[0]],[[-578,0],[0,0]],[[0,0],[0,0]],[[-4148,0],[0,0]],[[0,0],[0,0]],[[-16354,0],[0,0]],[[0,0],[0,0]],[[-38624,0],[0,0]],[[0,0],[0,0]],[[-55896,-34],[-34,0]],[[0,0],[0,0]],[[-48620,-272],[-272,0]],[[0,0],[0,0]],[[-23698,-748],[-748,0]],[[0,0],[0,0]],[[-5406,-816],[-816,0]],[[0,0],[0,0]],[[-306,-306],[-306,0]],[[0],[0,0]],[[0],[0,-34]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
