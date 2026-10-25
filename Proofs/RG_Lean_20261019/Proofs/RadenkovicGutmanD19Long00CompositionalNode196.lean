/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode195
import Proofs.RadenkovicGutmanD19Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e196 : NestedArithmetic.Expr 3 := .times e195 e003
noncomputable def p196 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[76,0],[0]],[[0,0],[0]],[[1140,0],[0]],[[0,0],[0]],[[7144,0],[0]],[[0,0],[0]],[[24244,0],[0]],[[0,0],[0]],[[48336,0],[0]],[[0,0],[0]],[[57532,38],[38]],[[0,0],[0]],[[39672,266],[266]],[[0,0],[0]],[[14364,608],[608]],[[0,0],[0]],[[2052,494],[494]],[[0,0],[0]],[[0,114],[114]]]
theorem step196 : p196=NestedArithmetic.mul p195 p003 := by decide +kernel
#print axioms step196
theorem h196 : NestedArithmetic.compile e196=p196 := StagedExprCompile.compile_times e196 e195 e003 p195 p003 p196 rfl h195 h003 step196
#print axioms h196
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
