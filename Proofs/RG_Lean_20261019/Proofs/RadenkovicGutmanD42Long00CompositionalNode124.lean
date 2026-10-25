/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode002
import Proofs.RadenkovicGutmanD42Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e124 : NestedArithmetic.Expr 3 := .times e002 e120
noncomputable def p124 : NestedHorner.Poly 3 := [[[3]]]
theorem step124 : p124=NestedArithmetic.mul p002 p120 := by decide +kernel
#print axioms step124
theorem h124 : NestedArithmetic.compile e124=p124 := StagedExprCompile.compile_times e124 e002 e120 p002 p120 p124 rfl h002 h120 step124
#print axioms h124
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
