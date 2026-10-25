/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode127
import Proofs.RadenkovicGutmanD39Long00CompositionalNode128
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e129 : NestedArithmetic.Expr 3 := .plus e127 e128
noncomputable def p129 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step129 : p129=NestedHorner.add p127 p128 := by decide +kernel
#print axioms step129
theorem h129 : NestedArithmetic.compile e129=p129 := StagedExprCompile.compile_plus e129 e127 e128 p127 p128 p129 rfl h127 h128 step129
#print axioms h129
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
