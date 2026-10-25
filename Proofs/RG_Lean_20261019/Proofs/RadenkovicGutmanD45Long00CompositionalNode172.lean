/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode171
import Proofs.RadenkovicGutmanD45Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[90,0],[0]],[[0,0],[0]],[[1350,0],[0]],[[0,0],[0]],[[8460,0],[0]],[[0,0],[0]],[[28710,0],[0]],[[0,0],[0]],[[57240,0],[0]],[[0,0],[0]],[[68130,45],[45]],[[0,0],[0]],[[46980,315],[315]],[[0,0],[0]],[[17010,720],[720]],[[0,0],[0]],[[2430,585],[585]],[[0,0],[0]],[[0,135],[135]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
