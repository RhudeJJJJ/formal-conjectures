/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode198
import Proofs.RadenkovicGutmanD18Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[124,0],[0,0]],[[0,0],[0,0]],[[1594,0],[0,0]],[[0,0],[0,0]],[[9422,0],[0,0]],[[0,0],[0,0]],[[30982,0],[0,0]],[[0,0],[0,0]],[[60528,2],[2,0]],[[0,0],[0,0]],[[70972,70],[70,0]],[[0,0],[0,0]],[[48230,440],[440,0]],[[0,0],[0,0]],[[16932,1020],[1020,0]],[[0,0],[0,0]],[[2016,918],[918,0]],[[0,0],[0,0]],[[-162,270],[270,2]],[[0],[0,0]],[[0],[0,18]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
