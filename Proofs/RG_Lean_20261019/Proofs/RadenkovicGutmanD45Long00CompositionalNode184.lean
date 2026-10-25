/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode030
import Proofs.RadenkovicGutmanD45Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[45],[0]],[[0,0],[0]],[[720,0],[0]],[[0,0],[0]],[[4815,0],[0]],[[0,0],[0]],[[17460,0],[0]],[[0,0],[0]],[[37260,0],[0]],[[0,0],[0]],[[47520,45],[45]],[[0,0],[0]],[[35055,315],[315]],[[0,0],[0]],[[13500,720],[720]],[[0,0],[0]],[[2025,585],[585]],[[0,0],[0]],[[0,135],[135]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
