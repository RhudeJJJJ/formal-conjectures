/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode198
import Proofs.RadenkovicGutmanD28Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[174,0],[0,0]],[[0,0],[0,0]],[[2344,0],[0,0]],[[0,0],[0,0]],[[14122,0],[0,0]],[[0,0],[0,0]],[[46932,0],[0,0]],[[0,0],[0,0]],[[92328,2],[2,0]],[[0,0],[0,0]],[[108812,100],[100,0]],[[0,0],[0,0]],[[74250,660],[660,0]],[[0,0],[0,0]],[[26162,1560],[1560,0]],[[0,0],[0,0]],[[3126,1418],[1418,0]],[[0,0],[0,0]],[[-252,420],[420,2]],[[0],[0,0]],[[0],[0,28]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
