/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode017
import Proofs.RadenkovicGutmanD21Long00CompositionalNode006
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e119 : NestedArithmetic.Expr 3 := .times e017 e006
noncomputable def p119 : NestedHorner.Poly 3 := [[[2]]]
theorem step119 : p119=NestedArithmetic.mul p017 p006 := by decide +kernel
#print axioms step119
theorem h119 : NestedArithmetic.compile e119=p119 := StagedExprCompile.compile_times e119 e017 e006 p017 p006 p119 rfl h017 h006 step119
#print axioms h119
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
