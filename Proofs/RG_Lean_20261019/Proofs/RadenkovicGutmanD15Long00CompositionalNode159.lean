/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode037
import Proofs.RadenkovicGutmanD15Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-13],[0]],[[0,0],[0]],[[-195,0],[0,0]],[[0,0],[0,0]],[[-1222,0],[0,0]],[[0,0],[0,0]],[[-4147,0],[0,0]],[[0,0],[0,0]],[[-8268,0],[0,0]],[[0,0],[0,0]],[[-9828,-13],[-13,0]],[[0,0],[0,0]],[[-6682,-104],[-104,0]],[[0,0],[0,0]],[[-2171,-286],[-286,0]],[[0,0],[0,0]],[[-39,-312],[-312,0]],[[0,0],[0,0]],[[117,-117],[-117,0]],[[0],[0,0]],[[0],[0,-13]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
