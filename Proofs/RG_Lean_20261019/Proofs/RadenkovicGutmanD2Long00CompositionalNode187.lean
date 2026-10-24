/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode137
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e187 : NestedArithmetic.Expr 3 := .times e137 e120
noncomputable def p187 : NestedHorner.Poly 3 := [[[2]]]
theorem step187 : p187=NestedArithmetic.mul p137 p120 := by decide +kernel
#print axioms step187
theorem h187 : NestedArithmetic.compile e187=p187 := StagedExprCompile.compile_times e187 e137 e120 p137 p120 p187 rfl h137 h120 step187
#print axioms h187
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
