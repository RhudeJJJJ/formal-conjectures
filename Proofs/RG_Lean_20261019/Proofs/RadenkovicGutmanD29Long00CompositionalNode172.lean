/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode171
import Proofs.RadenkovicGutmanD29Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[58,0],[0]],[[0,0],[0]],[[870,0],[0]],[[0,0],[0]],[[5452,0],[0]],[[0,0],[0]],[[18502,0],[0]],[[0,0],[0]],[[36888,0],[0]],[[0,0],[0]],[[43906,29],[29]],[[0,0],[0]],[[30276,203],[203]],[[0,0],[0]],[[10962,464],[464]],[[0,0],[0]],[[1566,377],[377]],[[0,0],[0]],[[0,87],[87]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
