/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e111 : NestedArithmetic.Expr 3 := .pow e032 2
noncomputable def p111 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,9]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-162,162],[0,162]],[[0,0,0],[0,0,0],[0,0]],[[729,-1458,729],[-1458,1512,432],[729,432]],[[0,0,0],[0,0,0],[0,0]],[[-486,-3402,3888],[-3402,10782,396],[3888,396]],[[0,0,0],[0,0,0],[0,0]],[[-26973,24786,8748],[24786,26748,144],[8748,144]],[[0,0,0],[0,0,0],[0,0]],[[-74250,155304,10800],[155304,35208,18],[10800,18]],[[0,0,0],[0,0],[0]],[[156285,410922,7974],[410922,27396],[7974]],[[0,0,0],[0,0],[0]],[[1482876,657270,3600],[657270,12942],[3600]],[[0,0,0],[0,0],[0]],[[4632966,702828,972],[702828,3636],[972]],[[0,0,0],[0,0],[0]],[[8908326,523008,144],[523008,558],[144]],[[0,0,0],[0,0],[0]],[[11989656,274554,9],[274554,36],[9]],[[0,0],[0]],[[11889288,101250],[101250]],[[0,0],[0]],[[8896248,25650],[25650]],[[0,0],[0]],[[5072850,4248],[4248]],[[0,0],[0]],[[2205333,414],[414]],[[0,0],[0]],[[725076,18],[18]],[[0]],[[177102]],[[0]],[[31122]],[[0]],[[3717]],[[0]],[[270]],[[0]],[[9]]]
theorem step111 : p111=NestedArithmetic.power p032 2 := by decide +kernel
#print axioms step111
theorem h111 : NestedArithmetic.compile e111=p111 := StagedExprCompile.compile_pow 2 e111 e032 p032 p111 rfl h032 step111
#print axioms h111
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
