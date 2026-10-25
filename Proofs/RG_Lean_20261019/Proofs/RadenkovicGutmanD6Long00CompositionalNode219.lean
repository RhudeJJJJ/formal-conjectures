/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode065
import Proofs.RadenkovicGutmanD6Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[6],[0]],[[0,0],[0]],[[96,0],[0]],[[0,0],[0]],[[642,0],[0]],[[0,0],[0]],[[2328,0],[0]],[[0,0],[0]],[[4968,0],[0]],[[0,0],[0]],[[6336,6],[6]],[[0,0],[0]],[[4674,42],[42]],[[0,0],[0]],[[1800,96],[96]],[[0,0],[0]],[[270,78],[78]],[[0,0],[0]],[[0,18],[18]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
