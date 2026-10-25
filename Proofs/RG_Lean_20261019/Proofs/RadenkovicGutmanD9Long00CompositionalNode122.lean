/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e122 : NestedArithmetic.Expr 3 := .pow e000 0
noncomputable def p122 : NestedHorner.Poly 3 := [[[1]]]
theorem step122 : p122=NestedArithmetic.power p000 0 := by decide +kernel
#print axioms step122
theorem h122 : NestedArithmetic.compile e122=p122 := StagedExprCompile.compile_pow 0 e122 e000 p000 p122 rfl h000 step122
#print axioms h122
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
