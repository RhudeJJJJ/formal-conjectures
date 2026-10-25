/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode194
import Proofs.RadenkovicGutmanD7Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[28],[0]],[[0,0],[0]],[[420,0],[0]],[[0,0],[0]],[[2632,0],[0]],[[0,0],[0]],[[8932,0],[0]],[[0,0],[0]],[[17808,0],[0]],[[0,0],[0]],[[21196,14],[14]],[[0,0],[0]],[[14616,98],[98]],[[0,0],[0]],[[5292,224],[224]],[[0,0],[0]],[[756,182],[182]],[[0,0],[0]],[[0,42],[42]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
