/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e001 : NestedArithmetic.Expr 3 := .pow e000 4
noncomputable def p001 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[0]],[[1]]]
theorem step001 : p001=NestedArithmetic.power p000 4 := by decide +kernel
#print axioms step001
theorem h001 : NestedArithmetic.compile e001=p001 := StagedExprCompile.compile_pow 4 e001 e000 p000 p001 rfl h000 step001
#print axioms h001
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
