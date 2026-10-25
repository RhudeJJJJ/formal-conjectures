/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode030
import Proofs.RadenkovicGutmanD39Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,39]],[[0,0],[0]],[[351,351],[351]],[[0,0],[0]],[[6201,936],[936]],[[0,0],[0]],[[27183,858],[858]],[[0,0],[0]],[[55770,312],[312]],[[0,0],[0]],[[64116,39],[39]],[[0]],[[44304]],[[0]],[[18759]],[[0]],[[4758]],[[0]],[[663]],[[0]],[[39]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
