/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode189
import Proofs.RadenkovicGutmanD19Long00CompositionalNode190
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e191 : NestedArithmetic.Expr 3 := .plus e189 e190
noncomputable def p191 : NestedHorner.Poly 3 := [[[2]],[[0]],[[19]]]
theorem step191 : p191=NestedHorner.add p189 p190 := by decide +kernel
#print axioms step191
theorem h191 : NestedArithmetic.compile e191=p191 := StagedExprCompile.compile_plus e191 e189 e190 p189 p190 p191 rfl h189 h190 step191
#print axioms h191
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
