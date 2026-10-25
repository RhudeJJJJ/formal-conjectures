/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode000
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e146 : NestedArithmetic.Expr 3 := .pow e000 10
noncomputable def p146 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[0]],[[1]]]
theorem step146 : p146=NestedArithmetic.power p000 10 := by decide +kernel
#print axioms step146
theorem h146 : NestedArithmetic.compile e146=p146 := StagedExprCompile.compile_pow 10 e146 e000 p000 p146 rfl h000 step146
#print axioms h146
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
