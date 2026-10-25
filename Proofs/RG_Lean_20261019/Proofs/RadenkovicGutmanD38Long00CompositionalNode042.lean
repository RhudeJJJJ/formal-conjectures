/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode030
import Proofs.RadenkovicGutmanD38Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e042 : NestedArithmetic.Expr 3 := .times e030 e028
noncomputable def p042 : NestedHorner.Poly 3 := [[[0],[0]],[[0,114],[114]],[[0,0],[0]],[[2052,494],[494]],[[0,0],[0]],[[14364,608],[608]],[[0,0],[0]],[[39672,266],[266]],[[0,0],[0]],[[57532,38],[38]],[[0]],[[48336]],[[0]],[[24244]],[[0]],[[7144]],[[0]],[[1140]],[[0]],[[76]]]
theorem step042 : p042=NestedArithmetic.mul p030 p028 := by decide +kernel
#print axioms step042
theorem h042 : NestedArithmetic.compile e042=p042 := StagedExprCompile.compile_times e042 e030 e028 p030 p028 p042 rfl h030 h028 step042
#print axioms h042
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
