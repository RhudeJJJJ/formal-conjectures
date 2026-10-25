/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode037
import Proofs.RadenkovicGutmanD33Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-31],[0]],[[0,0],[0]],[[-465,0],[0,0]],[[0,0],[0,0]],[[-2914,0],[0,0]],[[0,0],[0,0]],[[-9889,0],[0,0]],[[0,0],[0,0]],[[-19716,0],[0,0]],[[0,0],[0,0]],[[-23436,-31],[-31,0]],[[0,0],[0,0]],[[-15934,-248],[-248,0]],[[0,0],[0,0]],[[-5177,-682],[-682,0]],[[0,0],[0,0]],[[-93,-744],[-744,0]],[[0,0],[0,0]],[[279,-279],[-279,0]],[[0],[0,0]],[[0],[0,-31]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
