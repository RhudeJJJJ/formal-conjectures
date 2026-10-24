/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode136
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e137 : NestedArithmetic.Expr 3 := .times e136 e121
noncomputable def p137 : NestedHorner.Poly 3 := [[[1]],[[0]],[[7]],[[0]],[[16]],[[0]],[[13]],[[0]],[[3]]]
theorem step137 : p137=NestedArithmetic.mul p136 p121 := by decide +kernel
#print axioms step137
theorem h137 : NestedArithmetic.compile e137=p137 := StagedExprCompile.compile_times e137 e136 e121 p136 p121 p137 rfl h136 h121 step137
#print axioms h137
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
