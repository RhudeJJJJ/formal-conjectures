/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode065
import Proofs.RadenkovicGutmanD30Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[30],[0]],[[0,0],[0]],[[480,0],[0]],[[0,0],[0]],[[3210,0],[0]],[[0,0],[0]],[[11640,0],[0]],[[0,0],[0]],[[24840,0],[0]],[[0,0],[0]],[[31680,30],[30]],[[0,0],[0]],[[23370,210],[210]],[[0,0],[0]],[[9000,480],[480]],[[0,0],[0]],[[1350,390],[390]],[[0,0],[0]],[[0,90],[90]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
