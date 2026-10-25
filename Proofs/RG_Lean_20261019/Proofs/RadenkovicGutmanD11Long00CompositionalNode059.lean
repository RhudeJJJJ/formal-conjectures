/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode058
import Proofs.RadenkovicGutmanD11Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-18]],[[0,0],[0]],[[-162,-162],[-162]],[[0,0],[0]],[[-2862,-432],[-432]],[[0,0],[0]],[[-12546,-396],[-396]],[[0,0],[0]],[[-25740,-144],[-144]],[[0,0],[0]],[[-29592,-18],[-18]],[[0]],[[-20448]],[[0]],[[-8658]],[[0]],[[-2196]],[[0]],[[-306]],[[0]],[[-18]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
