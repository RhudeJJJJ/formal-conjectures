/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode198
import Proofs.RadenkovicGutmanD16Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[114,0],[0,0]],[[0,0],[0,0]],[[1444,0],[0,0]],[[0,0],[0,0]],[[8482,0],[0,0]],[[0,0],[0,0]],[[27792,0],[0,0]],[[0,0],[0,0]],[[54168,2],[2,0]],[[0,0],[0,0]],[[63404,64],[64,0]],[[0,0],[0,0]],[[43026,396],[396,0]],[[0,0],[0,0]],[[15086,912],[912,0]],[[0,0],[0,0]],[[1794,818],[818,0]],[[0,0],[0,0]],[[-144,240],[240,2]],[[0],[0,0]],[[0],[0,16]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
