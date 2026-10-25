/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode065
import Proofs.RadenkovicGutmanD29Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[29],[0]],[[0,0],[0]],[[464,0],[0]],[[0,0],[0]],[[3103,0],[0]],[[0,0],[0]],[[11252,0],[0]],[[0,0],[0]],[[24012,0],[0]],[[0,0],[0]],[[30624,29],[29]],[[0,0],[0]],[[22591,203],[203]],[[0,0],[0]],[[8700,464],[464]],[[0,0],[0]],[[1305,377],[377]],[[0,0],[0]],[[0,87],[87]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
