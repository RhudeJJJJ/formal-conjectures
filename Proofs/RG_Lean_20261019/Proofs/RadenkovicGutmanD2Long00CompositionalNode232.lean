/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode210
import Proofs.RadenkovicGutmanD2Long00CompositionalNode216
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e232 : NestedArithmetic.Expr 3 := .times e210 e216
noncomputable def p232 : NestedHorner.Poly 3 := [[[4],[0],[0]],[[0,0],[0,0],[0]],[[124,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1764,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[15264,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[89784,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[380052,8,0],[8,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1195540,184,0],[184,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2845728,1888,0],[1888,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[5168976,11400,0],[11400,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[7169200,45000,0],[45000,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[7537100,122028,4],[122028,12,0],[4,0]],[[0,0,0],[0,0,0],[0,0]],[[5901360,232516,60],[232516,184,0],[60,0]],[[0,0,0],[0,0,0],[0,0]],[[3324680,312856,376],[312856,1180,0],[376,0]],[[0,0,0],[0,0,0],[0,0]],[[1256116,294044,1276],[294044,4104,0],[1276,0]],[[0,0,0],[0,0,0],[0,0]],[[264252,187176,2544],[187176,8400,0],[2544,0]],[[0,0,0],[0,0,0],[0,0]],[[5616,75596,3028],[75596,10280,4],[3028,4]],[[0,0,0],[0,0,0],[0,0]],[[-10260,16704,2088],[16704,7292,28],[2088,28]],[[0,0,0],[0,0,0],[0,0]],[[-1620,1188,756],[1188,2712,64],[756,64]],[[0,0,0],[0,0,0],[0,0]],[[0,-108,108],[-108,396,52],[108,52]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,12],[0,12]]]
theorem step232 : p232=NestedArithmetic.mul p210 p216 := by decide +kernel
#print axioms step232
theorem h232 : NestedArithmetic.compile e232=p232 := StagedExprCompile.compile_times e232 e210 e216 p210 p216 p232 rfl h210 h216 step232
#print axioms h232
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
