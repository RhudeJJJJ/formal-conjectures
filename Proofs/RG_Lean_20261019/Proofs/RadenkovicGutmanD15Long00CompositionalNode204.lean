/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode194
import Proofs.RadenkovicGutmanD15Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e204 : NestedArithmetic.Expr 3 := .times e194 e183
noncomputable def p204 : NestedHorner.Poly 3 := [[[30],[0]],[[0,0],[0]],[[480,0],[0]],[[0,0],[0]],[[3210,0],[0]],[[0,0],[0]],[[11640,0],[0]],[[0,0],[0]],[[24840,0],[0]],[[0,0],[0]],[[31680,30],[30]],[[0,0],[0]],[[23370,210],[210]],[[0,0],[0]],[[9000,480],[480]],[[0,0],[0]],[[1350,390],[390]],[[0,0],[0]],[[0,90],[90]]]
theorem step204 : p204=NestedArithmetic.mul p194 p183 := by decide +kernel
#print axioms step204
theorem h204 : NestedArithmetic.compile e204=p204 := StagedExprCompile.compile_times e204 e194 e183 p194 p183 p204 rfl h194 h183 step204
#print axioms h204
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
