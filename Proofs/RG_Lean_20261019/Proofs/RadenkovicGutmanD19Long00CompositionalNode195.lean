/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode194
import Proofs.RadenkovicGutmanD19Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[76],[0]],[[0,0],[0]],[[1140,0],[0]],[[0,0],[0]],[[7144,0],[0]],[[0,0],[0]],[[24244,0],[0]],[[0,0],[0]],[[48336,0],[0]],[[0,0],[0]],[[57532,38],[38]],[[0,0],[0]],[[39672,266],[266]],[[0,0],[0]],[[14364,608],[608]],[[0,0],[0]],[[2052,494],[494]],[[0,0],[0]],[[0,114],[114]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
