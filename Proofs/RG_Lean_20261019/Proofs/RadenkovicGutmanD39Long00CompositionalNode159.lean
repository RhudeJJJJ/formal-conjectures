/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode037
import Proofs.RadenkovicGutmanD39Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-37],[0]],[[0,0],[0]],[[-555,0],[0,0]],[[0,0],[0,0]],[[-3478,0],[0,0]],[[0,0],[0,0]],[[-11803,0],[0,0]],[[0,0],[0,0]],[[-23532,0],[0,0]],[[0,0],[0,0]],[[-27972,-37],[-37,0]],[[0,0],[0,0]],[[-19018,-296],[-296,0]],[[0,0],[0,0]],[[-6179,-814],[-814,0]],[[0,0],[0,0]],[[-111,-888],[-888,0]],[[0,0],[0,0]],[[333,-333],[-333,0]],[[0],[0,0]],[[0],[0,-37]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
