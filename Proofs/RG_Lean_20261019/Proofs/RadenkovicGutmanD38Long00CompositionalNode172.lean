/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode171
import Proofs.RadenkovicGutmanD38Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[76,0],[0]],[[0,0],[0]],[[1140,0],[0]],[[0,0],[0]],[[7144,0],[0]],[[0,0],[0]],[[24244,0],[0]],[[0,0],[0]],[[48336,0],[0]],[[0,0],[0]],[[57532,38],[38]],[[0,0],[0]],[[39672,266],[266]],[[0,0],[0]],[[14364,608],[608]],[[0,0],[0]],[[2052,494],[494]],[[0,0],[0]],[[0,114],[114]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
