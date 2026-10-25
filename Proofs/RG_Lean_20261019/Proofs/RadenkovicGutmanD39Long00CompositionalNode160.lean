/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode159
import Proofs.RadenkovicGutmanD39Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-37],[0]],[[0,0],[0]],[[-555,0],[0,0]],[[0,0],[0,0]],[[-3478,0],[0,0]],[[0,0],[0,0]],[[-11803,0],[0,0]],[[0,0],[0,0]],[[-23532,0],[0,0]],[[0,0],[0,0]],[[-27972,-37],[-37,0]],[[0,0],[0,0]],[[-19018,-296],[-296,0]],[[0,0],[0,0]],[[-6179,-814],[-814,0]],[[0,0],[0,0]],[[-111,-888],[-888,0]],[[0,0],[0,0]],[[333,-333],[-333,0]],[[0],[0,0]],[[0],[0,-37]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
