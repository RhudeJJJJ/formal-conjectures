/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode006
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e118 : NestedArithmetic.Expr 3 := .pow e006 2
noncomputable def p118 : NestedHorner.Poly 3 := [[[1]]]
theorem step118 : p118=NestedArithmetic.power p006 2 := by decide +kernel
#print axioms step118
theorem h118 : NestedArithmetic.compile e118=p118 := StagedExprCompile.compile_pow 2 e118 e006 p006 p118 rfl h006 step118
#print axioms h118
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
