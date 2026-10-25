/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode164
import Proofs.RadenkovicGutmanD22Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-40],[0]],[[0,0],[0]],[[-592,0],[0,0]],[[0,0],[0,0]],[[-3648,0],[0,0]],[[0,0],[0,0]],[[-12112,0],[0,0]],[[0,0],[0,0]],[[-23440,0],[0,0]],[[0,0],[0,0]],[[-26688,-40],[-40,0]],[[0,0],[0,0]],[[-16896,-320],[-320,0]],[[0,0],[0,0]],[[-4560,-880],[-880,0]],[[0,0],[0,0]],[[504,-960],[-960,0]],[[0,0],[0,0]],[[432,-360],[-360,0]],[[0],[0,0]],[[0],[0,-40]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
