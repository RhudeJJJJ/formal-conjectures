/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode002
import Proofs.RadenkovicGutmanD4Long00CompositionalNode119
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e123 : NestedArithmetic.Expr 3 := .times e002 e119
noncomputable def p123 : NestedHorner.Poly 3 := [[[3]]]
theorem step123 : p123=NestedArithmetic.mul p002 p119 := by decide +kernel
#print axioms step123
theorem h123 : NestedArithmetic.compile e123=p123 := StagedExprCompile.compile_times e123 e002 e119 p002 p119 p123 rfl h002 h119 step123
#print axioms h123
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
