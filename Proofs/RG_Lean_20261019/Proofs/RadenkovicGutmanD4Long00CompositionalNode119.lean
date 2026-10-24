/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode006
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e119 : NestedArithmetic.Expr 3 := .pow e006 2
noncomputable def p119 : NestedHorner.Poly 3 := [[[1]]]
theorem step119 : p119=NestedArithmetic.power p006 2 := by decide +kernel
#print axioms step119
theorem h119 : NestedArithmetic.compile e119=p119 := StagedExprCompile.compile_pow 2 e119 e006 p006 p119 rfl h006 step119
#print axioms h119
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
