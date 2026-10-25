/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode065
import Proofs.RadenkovicGutmanD17Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[17],[0]],[[0,0],[0]],[[272,0],[0]],[[0,0],[0]],[[1819,0],[0]],[[0,0],[0]],[[6596,0],[0]],[[0,0],[0]],[[14076,0],[0]],[[0,0],[0]],[[17952,17],[17]],[[0,0],[0]],[[13243,119],[119]],[[0,0],[0]],[[5100,272],[272]],[[0,0],[0]],[[765,221],[221]],[[0,0],[0]],[[0,51],[51]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
