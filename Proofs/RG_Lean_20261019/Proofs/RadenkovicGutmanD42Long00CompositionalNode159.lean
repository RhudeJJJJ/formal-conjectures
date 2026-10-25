/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode037
import Proofs.RadenkovicGutmanD42Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-40],[0]],[[0,0],[0]],[[-600,0],[0,0]],[[0,0],[0,0]],[[-3760,0],[0,0]],[[0,0],[0,0]],[[-12760,0],[0,0]],[[0,0],[0,0]],[[-25440,0],[0,0]],[[0,0],[0,0]],[[-30240,-40],[-40,0]],[[0,0],[0,0]],[[-20560,-320],[-320,0]],[[0,0],[0,0]],[[-6680,-880],[-880,0]],[[0,0],[0,0]],[[-120,-960],[-960,0]],[[0,0],[0,0]],[[360,-360],[-360,0]],[[0],[0,0]],[[0],[0,-40]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
