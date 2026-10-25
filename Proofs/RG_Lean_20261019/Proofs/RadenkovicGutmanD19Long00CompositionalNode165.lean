/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode164
import Proofs.RadenkovicGutmanD19Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-34],[0]],[[0,0],[0]],[[-502,0],[0,0]],[[0,0],[0,0]],[[-3084,0],[0,0]],[[0,0],[0,0]],[[-10198,0],[0,0]],[[0,0],[0,0]],[[-19624,0],[0,0]],[[0,0],[0,0]],[[-22152,-34],[-34,0]],[[0,0],[0,0]],[[-13812,-272],[-272,0]],[[0,0],[0,0]],[[-3558,-748],[-748,0]],[[0,0],[0,0]],[[522,-816],[-816,0]],[[0,0],[0,0]],[[378,-306],[-306,0]],[[0],[0,0]],[[0],[0,-34]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
