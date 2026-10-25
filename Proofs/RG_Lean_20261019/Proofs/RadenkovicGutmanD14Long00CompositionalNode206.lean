/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode203
import Proofs.RadenkovicGutmanD14Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[76,0],[0,0]],[[0,0],[0,0]],[[930,0],[0,0]],[[0,0],[0,0]],[[5666,0],[0,0]],[[0,0],[0,0]],[[19870,0],[0,0]],[[0,0],[0,0]],[[42376,2],[2,0]],[[0,0],[0,0]],[[55444,58],[58,0]],[[0,0],[0,0]],[[43226,352],[352,0]],[[0,0],[0,0]],[[18476,804],[804,0]],[[0,0],[0,0]],[[3504,718],[718,0]],[[0,0],[0,0]],[[126,210],[210,2]],[[0],[0,0]],[[0],[0,14]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
