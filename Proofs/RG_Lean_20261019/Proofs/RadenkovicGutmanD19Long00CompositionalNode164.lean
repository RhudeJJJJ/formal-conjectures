/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode119
import Proofs.RadenkovicGutmanD19Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-34],[0]],[[0,0],[0]],[[-502,0],[0,0]],[[0,0],[0,0]],[[-3084,0],[0,0]],[[0,0],[0,0]],[[-10198,0],[0,0]],[[0,0],[0,0]],[[-19624,0],[0,0]],[[0,0],[0,0]],[[-22152,-34],[-34,0]],[[0,0],[0,0]],[[-13812,-272],[-272,0]],[[0,0],[0,0]],[[-3558,-748],[-748,0]],[[0,0],[0,0]],[[522,-816],[-816,0]],[[0,0],[0,0]],[[378,-306],[-306,0]],[[0],[0,0]],[[0],[0,-34]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
