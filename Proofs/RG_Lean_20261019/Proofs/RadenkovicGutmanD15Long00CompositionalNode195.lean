/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode194
import Proofs.RadenkovicGutmanD15Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[60],[0]],[[0,0],[0]],[[900,0],[0]],[[0,0],[0]],[[5640,0],[0]],[[0,0],[0]],[[19140,0],[0]],[[0,0],[0]],[[38160,0],[0]],[[0,0],[0]],[[45420,30],[30]],[[0,0],[0]],[[31320,210],[210]],[[0,0],[0]],[[11340,480],[480]],[[0,0],[0]],[[1620,390],[390]],[[0,0],[0]],[[0,90],[90]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
