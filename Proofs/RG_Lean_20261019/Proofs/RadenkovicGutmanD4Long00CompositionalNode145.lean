/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e145 : NestedArithmetic.Expr 3 := .pow e000 10
noncomputable def p145 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[1]]]
theorem step145 : p145=NestedArithmetic.power p000 10 := by decide +kernel
#print axioms step145
theorem h145 : NestedArithmetic.compile e145=p145 := StagedExprCompile.compile_pow 10 e145 e000 p000 p145 rfl h000 step145
#print axioms h145
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
