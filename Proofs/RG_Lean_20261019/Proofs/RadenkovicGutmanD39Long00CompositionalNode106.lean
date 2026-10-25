/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode095
import Proofs.RadenkovicGutmanD39Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2808,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25272,-25272,0],[-25272,-24336,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-665496,-286416,0],[-286416,-82680,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6570720,-1389960,0],[-1389960,-142896,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-35409816,-3828240,0],[-3828240,-138528,0],[0,0]],[[0,0,0],[0,0],[0]],[[-121012008,-6692712,0],[-6692712,-78000],[0]],[[0,0,0],[0,0],[0]],[[-283757136,-7856160,0],[-7856160,-25272],[0]],[[0,0,0],[0,0],[0]],[[-478447008,-6372912,0],[-6372912,-4368],[0]],[[0,0,0],[0,0],[0]],[[-597412296,-3612960,0],[-3612960,-312],[0]],[[0,0,0],[0,0],[0]],[[-562707600,-1426152,0],[-1426152,0],[0]],[[0,0],[0]],[[-404069328,-383760],[-383760]],[[0,0],[0]],[[-222114048,-67080],[-67080]],[[0,0],[0]],[[-93266472,-6864],[-6864]],[[0,0],[0]],[[-29644680,-312],[-312]],[[0,0],[0]],[[-7003152,0],[0]],[[0]],[[-1190592]],[[0]],[[-137592]],[[0]],[[-9672]],[[0]],[[-312]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
