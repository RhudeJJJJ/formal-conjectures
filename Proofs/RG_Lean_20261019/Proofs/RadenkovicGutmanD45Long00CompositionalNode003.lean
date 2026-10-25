/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e003 : NestedArithmetic.Expr 3 := .pow e000 2
noncomputable def p003 : NestedHorner.Poly 3 := [[],[[]],[[1]]]
theorem step003 : p003=NestedArithmetic.power p000 2 := by decide +kernel
#print axioms step003
theorem h003 : NestedArithmetic.compile e003=p003 := StagedExprCompile.compile_pow 2 e003 e000 p000 p003 rfl h000 step003
#print axioms h003
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
