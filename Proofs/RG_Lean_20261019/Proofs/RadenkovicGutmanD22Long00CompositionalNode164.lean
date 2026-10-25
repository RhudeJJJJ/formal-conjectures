/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode119
import Proofs.RadenkovicGutmanD22Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-40],[0]],[[0,0],[0]],[[-592,0],[0,0]],[[0,0],[0,0]],[[-3648,0],[0,0]],[[0,0],[0,0]],[[-12112,0],[0,0]],[[0,0],[0,0]],[[-23440,0],[0,0]],[[0,0],[0,0]],[[-26688,-40],[-40,0]],[[0,0],[0,0]],[[-16896,-320],[-320,0]],[[0,0],[0,0]],[[-4560,-880],[-880,0]],[[0,0],[0,0]],[[504,-960],[-960,0]],[[0,0],[0,0]],[[432,-360],[-360,0]],[[0],[0,0]],[[0],[0,-40]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
