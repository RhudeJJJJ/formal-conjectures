/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode194
import Proofs.RadenkovicGutmanD35Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[140],[0]],[[0,0],[0]],[[2100,0],[0]],[[0,0],[0]],[[13160,0],[0]],[[0,0],[0]],[[44660,0],[0]],[[0,0],[0]],[[89040,0],[0]],[[0,0],[0]],[[105980,70],[70]],[[0,0],[0]],[[73080,490],[490]],[[0,0],[0]],[[26460,1120],[1120]],[[0,0],[0]],[[3780,910],[910]],[[0,0],[0]],[[0,210],[210]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
