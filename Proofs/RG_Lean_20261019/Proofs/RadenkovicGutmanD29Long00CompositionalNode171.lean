/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode030
import Proofs.RadenkovicGutmanD29Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[58],[0]],[[0,0],[0]],[[870,0],[0]],[[0,0],[0]],[[5452,0],[0]],[[0,0],[0]],[[18502,0],[0]],[[0,0],[0]],[[36888,0],[0]],[[0,0],[0]],[[43906,29],[29]],[[0,0],[0]],[[30276,203],[203]],[[0,0],[0]],[[10962,464],[464]],[[0,0],[0]],[[1566,377],[377]],[[0,0],[0]],[[0,87],[87]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
