/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode058
import Proofs.RadenkovicGutmanD9Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .times e058 e052
noncomputable def p059 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-14]],[[0,0],[0]],[[-126,-126],[-126]],[[0,0],[0]],[[-2226,-336],[-336]],[[0,0],[0]],[[-9758,-308],[-308]],[[0,0],[0]],[[-20020,-112],[-112]],[[0,0],[0]],[[-23016,-14],[-14]],[[0]],[[-15904]],[[0]],[[-6734]],[[0]],[[-1708]],[[0]],[[-238]],[[0]],[[-14]]]
theorem step059 : p059=NestedArithmetic.mul p058 p052 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_times e059 e058 e052 p058 p052 p059 rfl h058 h052 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
