/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode119
import Proofs.RadenkovicGutmanD25Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-46],[0]],[[0,0],[0]],[[-682,0],[0,0]],[[0,0],[0,0]],[[-4212,0],[0,0]],[[0,0],[0,0]],[[-14026,0],[0,0]],[[0,0],[0,0]],[[-27256,0],[0,0]],[[0,0],[0,0]],[[-31224,-46],[-46,0]],[[0,0],[0,0]],[[-19980,-368],[-368,0]],[[0,0],[0,0]],[[-5562,-1012],[-1012,0]],[[0,0],[0,0]],[[486,-1104],[-1104,0]],[[0,0],[0,0]],[[486,-414],[-414,0]],[[0],[0,0]],[[0],[0,-46]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
