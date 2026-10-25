/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode198
import Proofs.RadenkovicGutmanD44Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[254,0],[0,0]],[[0,0],[0,0]],[[3544,0],[0,0]],[[0,0],[0,0]],[[21642,0],[0,0]],[[0,0],[0,0]],[[72452,0],[0,0]],[[0,0],[0,0]],[[143208,2],[2,0]],[[0,0],[0,0]],[[169356,148],[148,0]],[[0,0],[0,0]],[[115882,1012],[1012,0]],[[0,0],[0,0]],[[40930,2424],[2424,0]],[[0,0],[0,0]],[[4902,2218],[2218,0]],[[0,0],[0,0]],[[-396,660],[660,2]],[[0],[0,0]],[[0],[0,44]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
