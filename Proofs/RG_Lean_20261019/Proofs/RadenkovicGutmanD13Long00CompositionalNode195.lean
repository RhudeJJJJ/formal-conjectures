/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode194
import Proofs.RadenkovicGutmanD13Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[52],[0]],[[0,0],[0]],[[780,0],[0]],[[0,0],[0]],[[4888,0],[0]],[[0,0],[0]],[[16588,0],[0]],[[0,0],[0]],[[33072,0],[0]],[[0,0],[0]],[[39364,26],[26]],[[0,0],[0]],[[27144,182],[182]],[[0,0],[0]],[[9828,416],[416]],[[0,0],[0]],[[1404,338],[338]],[[0,0],[0]],[[0,78],[78]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
