/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode037
import Proofs.RadenkovicGutmanD13Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-11],[0]],[[0,0],[0]],[[-165,0],[0,0]],[[0,0],[0,0]],[[-1034,0],[0,0]],[[0,0],[0,0]],[[-3509,0],[0,0]],[[0,0],[0,0]],[[-6996,0],[0,0]],[[0,0],[0,0]],[[-8316,-11],[-11,0]],[[0,0],[0,0]],[[-5654,-88],[-88,0]],[[0,0],[0,0]],[[-1837,-242],[-242,0]],[[0,0],[0,0]],[[-33,-264],[-264,0]],[[0,0],[0,0]],[[99,-99],[-99,0]],[[0],[0,0]],[[0],[0,-11]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
