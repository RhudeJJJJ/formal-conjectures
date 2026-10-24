/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode032
import Proofs.RadenkovicGutmanD2Long00CompositionalNode059
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e087 : NestedArithmetic.Expr 3 := .times e032 e059
noncomputable def p087 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,12],[0,12,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-108,108],[-108,396,52],[108,52]],[[0,0,0],[0,0,0],[0,0]],[[-1620,1188,756],[1188,2712,64],[756,64]],[[0,0,0],[0,0,0],[0,0]],[[-10260,16704,2088],[16704,7292,28],[2088,28]],[[0,0,0],[0,0,0],[0,0]],[[5616,75596,3028],[75596,10280,4],[3028,4]],[[0,0,0],[0,0,0],[0,0]],[[264252,187176,2544],[187176,8400,0],[2544,0]],[[0,0,0],[0,0],[0]],[[1256116,294044,1276],[294044,4104],[1276]],[[0,0,0],[0,0],[0]],[[3324680,312856,376],[312856,1180],[376]],[[0,0,0],[0,0],[0]],[[5901360,232516,60],[232516,184],[60]],[[0,0,0],[0,0],[0]],[[7537100,122028,4],[122028,12],[4]],[[0,0,0],[0,0],[0]],[[7169200,45000,0],[45000,0],[0]],[[0,0],[0]],[[5168976,11400],[11400]],[[0,0],[0]],[[2845728,1888],[1888]],[[0,0],[0]],[[1195540,184],[184]],[[0,0],[0]],[[380052,8],[8]],[[0,0],[0]],[[89784,0],[0]],[[0]],[[15264]],[[0]],[[1764]],[[0]],[[124]],[[0]],[[4]],[[0]],[[0]]]
theorem step087 : p087=NestedArithmetic.mul p032 p059 := by decide +kernel
#print axioms step087
theorem h087 : NestedArithmetic.compile e087=p087 := StagedExprCompile.compile_times e087 e032 e059 p032 p059 p087 rfl h032 h059 step087
#print axioms h087
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
