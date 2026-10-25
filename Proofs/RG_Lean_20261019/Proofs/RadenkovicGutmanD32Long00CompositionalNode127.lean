/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode126
import Proofs.RadenkovicGutmanD32Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e127 : NestedArithmetic.Expr 3 := .times e126 e122
noncomputable def p127 : NestedHorner.Poly 3 := [[[1]],[[0]],[[3]]]
theorem step127 : p127=NestedArithmetic.mul p126 p122 := by decide +kernel
#print axioms step127
theorem h127 : NestedArithmetic.compile e127=p127 := StagedExprCompile.compile_times e127 e126 e122 p126 p122 p127 rfl h126 h122 step127
#print axioms h127
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
