/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode198
import Proofs.RadenkovicGutmanD33Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[199,0],[0,0]],[[0,0],[0,0]],[[2719,0],[0,0]],[[0,0],[0,0]],[[16472,0],[0,0]],[[0,0],[0,0]],[[54907,0],[0,0]],[[0,0],[0,0]],[[108228,2],[2,0]],[[0,0],[0,0]],[[127732,115],[115,0]],[[0,0],[0,0]],[[87260,770],[770,0]],[[0,0],[0,0]],[[30777,1830],[1830,0]],[[0,0],[0,0]],[[3681,1668],[1668,0]],[[0,0],[0,0]],[[-297,495],[495,2]],[[0],[0,0]],[[0],[0,33]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
