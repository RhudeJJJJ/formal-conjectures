/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode120
import Proofs.RadenkovicGutmanD31Long00CompositionalNode129
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e130 : NestedArithmetic.Expr 3 := .times e120 e129
noncomputable def p130 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step130 : p130=NestedArithmetic.mul p120 p129 := by decide +kernel
#print axioms step130
theorem h130 : NestedArithmetic.compile e130=p130 := StagedExprCompile.compile_times e130 e120 e129 p120 p129 p130 rfl h120 h129 step130
#print axioms h130
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
