/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode198
import Proofs.RadenkovicGutmanD43Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[249,0],[0,0]],[[0,0],[0,0]],[[3469,0],[0,0]],[[0,0],[0,0]],[[21172,0],[0,0]],[[0,0],[0,0]],[[70857,0],[0,0]],[[0,0],[0,0]],[[140028,2],[2,0]],[[0,0],[0,0]],[[165572,145],[145,0]],[[0,0],[0,0]],[[113280,990],[990,0]],[[0,0],[0,0]],[[40007,2370],[2370,0]],[[0,0],[0,0]],[[4791,2168],[2168,0]],[[0,0],[0,0]],[[-387,645],[645,2]],[[0],[0,0]],[[0],[0,43]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
