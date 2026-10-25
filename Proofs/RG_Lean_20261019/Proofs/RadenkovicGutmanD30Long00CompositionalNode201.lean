/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode198
import Proofs.RadenkovicGutmanD30Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[184,0],[0,0]],[[0,0],[0,0]],[[2494,0],[0,0]],[[0,0],[0,0]],[[15062,0],[0,0]],[[0,0],[0,0]],[[50122,0],[0,0]],[[0,0],[0,0]],[[98688,2],[2,0]],[[0,0],[0,0]],[[116380,106],[106,0]],[[0,0],[0,0]],[[79454,704],[704,0]],[[0,0],[0,0]],[[28008,1668],[1668,0]],[[0,0],[0,0]],[[3348,1518],[1518,0]],[[0,0],[0,0]],[[-270,450],[450,2]],[[0],[0,0]],[[0],[0,30]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
