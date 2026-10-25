/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode037
import Proofs.RadenkovicGutmanD20Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-18],[0]],[[0,0],[0]],[[-270,0],[0,0]],[[0,0],[0,0]],[[-1692,0],[0,0]],[[0,0],[0,0]],[[-5742,0],[0,0]],[[0,0],[0,0]],[[-11448,0],[0,0]],[[0,0],[0,0]],[[-13608,-18],[-18,0]],[[0,0],[0,0]],[[-9252,-144],[-144,0]],[[0,0],[0,0]],[[-3006,-396],[-396,0]],[[0,0],[0,0]],[[-54,-432],[-432,0]],[[0,0],[0,0]],[[162,-162],[-162,0]],[[0],[0,0]],[[0],[0,-18]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
