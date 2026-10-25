/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode164
import Proofs.RadenkovicGutmanD25Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-46],[0]],[[0,0],[0]],[[-682,0],[0,0]],[[0,0],[0,0]],[[-4212,0],[0,0]],[[0,0],[0,0]],[[-14026,0],[0,0]],[[0,0],[0,0]],[[-27256,0],[0,0]],[[0,0],[0,0]],[[-31224,-46],[-46,0]],[[0,0],[0,0]],[[-19980,-368],[-368,0]],[[0,0],[0,0]],[[-5562,-1012],[-1012,0]],[[0,0],[0,0]],[[486,-1104],[-1104,0]],[[0,0],[0,0]],[[486,-414],[-414,0]],[[0],[0,0]],[[0],[0,-46]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
