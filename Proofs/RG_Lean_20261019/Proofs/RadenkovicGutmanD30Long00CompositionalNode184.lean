/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode030
import Proofs.RadenkovicGutmanD30Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .times e030 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[30],[0]],[[0,0],[0]],[[480,0],[0]],[[0,0],[0]],[[3210,0],[0]],[[0,0],[0]],[[11640,0],[0]],[[0,0],[0]],[[24840,0],[0]],[[0,0],[0]],[[31680,30],[30]],[[0,0],[0]],[[23370,210],[210]],[[0,0],[0]],[[9000,480],[480]],[[0,0],[0]],[[1350,390],[390]],[[0,0],[0]],[[0,90],[90]]]
theorem step184 : p184=NestedArithmetic.mul p030 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_times e184 e030 e183 p030 p183 p184 rfl h030 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
