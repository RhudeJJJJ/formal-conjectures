/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode198
import Proofs.RadenkovicGutmanD19Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[129,0],[0,0]],[[0,0],[0,0]],[[1669,0],[0,0]],[[0,0],[0,0]],[[9892,0],[0,0]],[[0,0],[0,0]],[[32577,0],[0,0]],[[0,0],[0,0]],[[63708,2],[2,0]],[[0,0],[0,0]],[[74756,73],[73,0]],[[0,0],[0,0]],[[50832,462],[462,0]],[[0,0],[0,0]],[[17855,1074],[1074,0]],[[0,0],[0,0]],[[2127,968],[968,0]],[[0,0],[0,0]],[[-171,285],[285,2]],[[0],[0,0]],[[0],[0,19]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
