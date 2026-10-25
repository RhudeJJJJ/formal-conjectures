/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode204
import Proofs.RadenkovicGutmanD15Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[30,0],[0]],[[0,0],[0]],[[480,0],[0]],[[0,0],[0]],[[3210,0],[0]],[[0,0],[0]],[[11640,0],[0]],[[0,0],[0]],[[24840,0],[0]],[[0,0],[0]],[[31680,30],[30]],[[0,0],[0]],[[23370,210],[210]],[[0,0],[0]],[[9000,480],[480]],[[0,0],[0]],[[1350,390],[390]],[[0,0],[0]],[[0,90],[90]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
