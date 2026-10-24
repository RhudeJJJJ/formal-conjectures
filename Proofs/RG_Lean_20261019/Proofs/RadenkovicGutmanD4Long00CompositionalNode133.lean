/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode132
import Proofs.RadenkovicGutmanD4Long00CompositionalNode121
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e133 : NestedArithmetic.Expr 3 := .times e132 e121
noncomputable def p133 : NestedHorner.Poly 3 := [[[1]],[[0]],[[4]]]
theorem step133 : p133=NestedArithmetic.mul p132 p121 := by decide +kernel
#print axioms step133
theorem h133 : NestedArithmetic.compile e133=p133 := StagedExprCompile.compile_times e133 e132 e121 p132 p121 p133 rfl h132 h121 step133
#print axioms h133
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
