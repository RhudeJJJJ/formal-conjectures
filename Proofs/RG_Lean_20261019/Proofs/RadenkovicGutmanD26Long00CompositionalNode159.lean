/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode037
import Proofs.RadenkovicGutmanD26Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-24],[0]],[[0,0],[0]],[[-360,0],[0,0]],[[0,0],[0,0]],[[-2256,0],[0,0]],[[0,0],[0,0]],[[-7656,0],[0,0]],[[0,0],[0,0]],[[-15264,0],[0,0]],[[0,0],[0,0]],[[-18144,-24],[-24,0]],[[0,0],[0,0]],[[-12336,-192],[-192,0]],[[0,0],[0,0]],[[-4008,-528],[-528,0]],[[0,0],[0,0]],[[-72,-576],[-576,0]],[[0,0],[0,0]],[[216,-216],[-216,0]],[[0],[0,0]],[[0],[0,-24]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
