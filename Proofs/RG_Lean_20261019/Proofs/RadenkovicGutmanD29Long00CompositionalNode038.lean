/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode037
import Proofs.RadenkovicGutmanD29Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e038 : NestedArithmetic.Expr 3 := .times e037 e032
noncomputable def p038 : NestedHorner.Poly 3 := [[[0],[0,-27]],[[0,0],[0]],[[243,-243],[-243]],[[0,0],[0]],[[-81,-648],[-648]],[[0,0],[0]],[[-4509,-594],[-594]],[[0,0],[0]],[[-13878,-216],[-216]],[[0,0],[0]],[[-20412,-27],[-27]],[[0]],[[-17172]],[[0]],[[-8613]],[[0]],[[-2538]],[[0]],[[-405]],[[0]],[[-27]]]
theorem step038 : p038=NestedArithmetic.mul p037 p032 := by decide +kernel
#print axioms step038
theorem h038 : NestedArithmetic.compile e038=p038 := StagedExprCompile.compile_times e038 e037 e032 p037 p032 p038 rfl h037 h032 step038
#print axioms h038
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
