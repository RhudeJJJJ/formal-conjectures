/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode037
import Proofs.RadenkovicGutmanD29Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-27],[0]],[[0,0],[0]],[[-405,0],[0,0]],[[0,0],[0,0]],[[-2538,0],[0,0]],[[0,0],[0,0]],[[-8613,0],[0,0]],[[0,0],[0,0]],[[-17172,0],[0,0]],[[0,0],[0,0]],[[-20412,-27],[-27,0]],[[0,0],[0,0]],[[-13878,-216],[-216,0]],[[0,0],[0,0]],[[-4509,-594],[-594,0]],[[0,0],[0,0]],[[-81,-648],[-648,0]],[[0,0],[0,0]],[[243,-243],[-243,0]],[[0],[0,0]],[[0],[0,-27]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
