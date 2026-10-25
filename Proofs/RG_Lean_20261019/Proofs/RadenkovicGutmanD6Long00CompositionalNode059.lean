/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode058
import Proofs.RadenkovicGutmanD6Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-8]],[[0,0],[0]],[[-72,-72],[-72]],[[0,0],[0]],[[-1272,-192],[-192]],[[0,0],[0]],[[-5576,-176],[-176]],[[0,0],[0]],[[-11440,-64],[-64]],[[0,0],[0]],[[-13152,-8],[-8]],[[0]],[[-9088]],[[0]],[[-3848]],[[0]],[[-976]],[[0]],[[-136]],[[0]],[[-8]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
