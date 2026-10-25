/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode058
import Proofs.RadenkovicGutmanD34Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-64]],[[0,0],[0]],[[-576,-576],[-576]],[[0,0],[0]],[[-10176,-1536],[-1536]],[[0,0],[0]],[[-44608,-1408],[-1408]],[[0,0],[0]],[[-91520,-512],[-512]],[[0,0],[0]],[[-105216,-64],[-64]],[[0]],[[-72704]],[[0]],[[-30784]],[[0]],[[-7808]],[[0]],[[-1088]],[[0]],[[-64]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
