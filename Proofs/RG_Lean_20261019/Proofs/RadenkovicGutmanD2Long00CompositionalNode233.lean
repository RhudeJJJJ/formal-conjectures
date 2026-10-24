/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode232
import Proofs.RadenkovicGutmanD2Long00CompositionalNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e233 : NestedArithmetic.Expr 3 := .times e232 e120
noncomputable def p233 : NestedHorner.Poly 3 := [[[4],[0],[0]],[[0,0],[0,0],[0]],[[124,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1764,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[15264,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[89784,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[380052,8,0],[8,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1195540,184,0],[184,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2845728,1888,0],[1888,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[5168976,11400,0],[11400,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[7169200,45000,0],[45000,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[7537100,122028,4],[122028,12,0],[4,0]],[[0,0,0],[0,0,0],[0,0]],[[5901360,232516,60],[232516,184,0],[60,0]],[[0,0,0],[0,0,0],[0,0]],[[3324680,312856,376],[312856,1180,0],[376,0]],[[0,0,0],[0,0,0],[0,0]],[[1256116,294044,1276],[294044,4104,0],[1276,0]],[[0,0,0],[0,0,0],[0,0]],[[264252,187176,2544],[187176,8400,0],[2544,0]],[[0,0,0],[0,0,0],[0,0]],[[5616,75596,3028],[75596,10280,4],[3028,4]],[[0,0,0],[0,0,0],[0,0]],[[-10260,16704,2088],[16704,7292,28],[2088,28]],[[0,0,0],[0,0,0],[0,0]],[[-1620,1188,756],[1188,2712,64],[756,64]],[[0,0,0],[0,0,0],[0,0]],[[0,-108,108],[-108,396,52],[108,52]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,12],[0,12]]]
theorem step233 : p233=NestedArithmetic.mul p232 p120 := by decide +kernel
#print axioms step233
theorem h233 : NestedArithmetic.compile e233=p233 := StagedExprCompile.compile_times e233 e232 e120 p232 p120 p233 rfl h232 h120 step233
#print axioms h233
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
