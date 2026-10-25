/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode065
import Proofs.RadenkovicGutmanD22Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[22],[0]],[[0,0],[0]],[[352,0],[0]],[[0,0],[0]],[[2354,0],[0]],[[0,0],[0]],[[8536,0],[0]],[[0,0],[0]],[[18216,0],[0]],[[0,0],[0]],[[23232,22],[22]],[[0,0],[0]],[[17138,154],[154]],[[0,0],[0]],[[6600,352],[352]],[[0,0],[0]],[[990,286],[286]],[[0,0],[0]],[[0,66],[66]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
