/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode065
import Proofs.RadenkovicGutmanD45Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[45],[0]],[[0,0],[0]],[[720,0],[0]],[[0,0],[0]],[[4815,0],[0]],[[0,0],[0]],[[17460,0],[0]],[[0,0],[0]],[[37260,0],[0]],[[0,0],[0]],[[47520,45],[45]],[[0,0],[0]],[[35055,315],[315]],[[0,0],[0]],[[13500,720],[720]],[[0,0],[0]],[[2025,585],[585]],[[0,0],[0]],[[0,135],[135]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
