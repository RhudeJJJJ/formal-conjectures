/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode047
import Proofs.RadenkovicGutmanD19Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e048 : NestedArithmetic.Expr 3 := .times e047 e028
noncomputable def p048 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,114],[114]],[[0,0],[0]],[[2052,494],[494]],[[0,0],[0]],[[14364,608],[608]],[[0,0],[0]],[[39672,266],[266]],[[0,0],[0]],[[57532,38],[38]],[[0]],[[48336]],[[0]],[[24244]],[[0]],[[7144]],[[0]],[[1140]],[[0]],[[76]]]
theorem step048 : p048=NestedArithmetic.mul p047 p028 := by decide +kernel
#print axioms step048
theorem h048 : NestedArithmetic.compile e048=p048 := StagedExprCompile.compile_times e048 e047 e028 p047 p028 p048 rfl h047 h028 step048
#print axioms h048
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
