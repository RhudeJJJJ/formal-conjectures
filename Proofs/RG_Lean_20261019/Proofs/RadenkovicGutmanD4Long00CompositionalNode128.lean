/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode126
import Proofs.RadenkovicGutmanD4Long00CompositionalNode127
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e128 : NestedArithmetic.Expr 3 := .plus e126 e127
noncomputable def p128 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]],[[0]],[[1]]]
theorem step128 : p128=NestedHorner.add p126 p127 := by decide +kernel
#print axioms step128
theorem h128 : NestedArithmetic.compile e128=p128 := StagedExprCompile.compile_plus e128 e126 e127 p126 p127 p128 rfl h126 h127 step128
#print axioms h128
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
