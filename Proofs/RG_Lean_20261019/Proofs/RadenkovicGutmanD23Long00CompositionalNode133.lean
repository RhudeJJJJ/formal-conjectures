/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode123
import Proofs.RadenkovicGutmanD23Long00CompositionalNode132
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e133 : NestedArithmetic.Expr 3 := .plus e123 e132
noncomputable def p133 : NestedHorner.Poly 3 := [[[1]],[[0]],[[4]]]
theorem step133 : p133=NestedHorner.add p123 p132 := by decide +kernel
#print axioms step133
theorem h133 : NestedArithmetic.compile e133=p133 := StagedExprCompile.compile_plus e133 e123 e132 p123 p132 p133 rfl h123 h132 step133
#print axioms h133
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
