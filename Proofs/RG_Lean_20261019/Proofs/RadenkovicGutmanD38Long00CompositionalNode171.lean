/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode030
import Proofs.RadenkovicGutmanD38Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[76],[0]],[[0,0],[0]],[[1140,0],[0]],[[0,0],[0]],[[7144,0],[0]],[[0,0],[0]],[[24244,0],[0]],[[0,0],[0]],[[48336,0],[0]],[[0,0],[0]],[[57532,38],[38]],[[0,0],[0]],[[39672,266],[266]],[[0,0],[0]],[[14364,608],[608]],[[0,0],[0]],[[2052,494],[494]],[[0,0],[0]],[[0,114],[114]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
