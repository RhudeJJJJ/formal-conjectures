/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode065
import Proofs.RadenkovicGutmanD36Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[36],[0]],[[0,0],[0]],[[576,0],[0]],[[0,0],[0]],[[3852,0],[0]],[[0,0],[0]],[[13968,0],[0]],[[0,0],[0]],[[29808,0],[0]],[[0,0],[0]],[[38016,36],[36]],[[0,0],[0]],[[28044,252],[252]],[[0,0],[0]],[[10800,576],[576]],[[0,0],[0]],[[1620,468],[468]],[[0,0],[0]],[[0,108],[108]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
