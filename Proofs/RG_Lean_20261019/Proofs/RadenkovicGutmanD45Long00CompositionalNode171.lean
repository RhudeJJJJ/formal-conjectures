/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode030
import Proofs.RadenkovicGutmanD45Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[90],[0]],[[0,0],[0]],[[1350,0],[0]],[[0,0],[0]],[[8460,0],[0]],[[0,0],[0]],[[28710,0],[0]],[[0,0],[0]],[[57240,0],[0]],[[0,0],[0]],[[68130,45],[45]],[[0,0],[0]],[[46980,315],[315]],[[0,0],[0]],[[17010,720],[720]],[[0,0],[0]],[[2430,585],[585]],[[0,0],[0]],[[0,135],[135]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
