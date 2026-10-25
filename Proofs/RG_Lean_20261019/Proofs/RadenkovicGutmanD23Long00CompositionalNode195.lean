/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode194
import Proofs.RadenkovicGutmanD23Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[92],[0]],[[0,0],[0]],[[1380,0],[0]],[[0,0],[0]],[[8648,0],[0]],[[0,0],[0]],[[29348,0],[0]],[[0,0],[0]],[[58512,0],[0]],[[0,0],[0]],[[69644,46],[46]],[[0,0],[0]],[[48024,322],[322]],[[0,0],[0]],[[17388,736],[736]],[[0,0],[0]],[[2484,598],[598]],[[0,0],[0]],[[0,138],[138]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
