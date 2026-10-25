/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode030
import Proofs.RadenkovicGutmanD29Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e042 : NestedArithmetic.Expr 3 := .times e030 e028
noncomputable def p042 : NestedHorner.Poly 3 := [[[0],[0]],[[0,87],[87]],[[0,0],[0]],[[1566,377],[377]],[[0,0],[0]],[[10962,464],[464]],[[0,0],[0]],[[30276,203],[203]],[[0,0],[0]],[[43906,29],[29]],[[0]],[[36888]],[[0]],[[18502]],[[0]],[[5452]],[[0]],[[870]],[[0]],[[58]]]
theorem step042 : p042=NestedArithmetic.mul p030 p028 := by decide +kernel
#print axioms step042
theorem h042 : NestedArithmetic.compile e042=p042 := StagedExprCompile.compile_times e042 e030 e028 p030 p028 p042 rfl h030 h028 step042
#print axioms h042
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
