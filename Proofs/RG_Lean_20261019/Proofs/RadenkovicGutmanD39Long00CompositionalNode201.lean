/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode198
import Proofs.RadenkovicGutmanD39Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[229,0],[0,0]],[[0,0],[0,0]],[[3169,0],[0,0]],[[0,0],[0,0]],[[19292,0],[0,0]],[[0,0],[0,0]],[[64477,0],[0,0]],[[0,0],[0,0]],[[127308,2],[2,0]],[[0,0],[0,0]],[[150436,133],[133,0]],[[0,0],[0,0]],[[102872,902],[902,0]],[[0,0],[0,0]],[[36315,2154],[2154,0]],[[0,0],[0,0]],[[4347,1968],[1968,0]],[[0,0],[0,0]],[[-351,585],[585,2]],[[0],[0,0]],[[0],[0,39]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
