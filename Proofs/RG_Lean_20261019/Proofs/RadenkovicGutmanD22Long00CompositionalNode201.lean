/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode198
import Proofs.RadenkovicGutmanD22Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[144,0],[0,0]],[[0,0],[0,0]],[[1894,0],[0,0]],[[0,0],[0,0]],[[11302,0],[0,0]],[[0,0],[0,0]],[[37362,0],[0,0]],[[0,0],[0,0]],[[73248,2],[2,0]],[[0,0],[0,0]],[[86108,82],[82,0]],[[0,0],[0,0]],[[58638,528],[528,0]],[[0,0],[0,0]],[[20624,1236],[1236,0]],[[0,0],[0,0]],[[2460,1118],[1118,0]],[[0,0],[0,0]],[[-198,330],[330,2]],[[0],[0,0]],[[0],[0,22]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
