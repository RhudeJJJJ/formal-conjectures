/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode037
import Proofs.RadenkovicGutmanD45Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-43],[0]],[[0,0],[0]],[[-645,0],[0,0]],[[0,0],[0,0]],[[-4042,0],[0,0]],[[0,0],[0,0]],[[-13717,0],[0,0]],[[0,0],[0,0]],[[-27348,0],[0,0]],[[0,0],[0,0]],[[-32508,-43],[-43,0]],[[0,0],[0,0]],[[-22102,-344],[-344,0]],[[0,0],[0,0]],[[-7181,-946],[-946,0]],[[0,0],[0,0]],[[-129,-1032],[-1032,0]],[[0,0],[0,0]],[[387,-387],[-387,0]],[[0],[0,0]],[[0],[0,-43]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
