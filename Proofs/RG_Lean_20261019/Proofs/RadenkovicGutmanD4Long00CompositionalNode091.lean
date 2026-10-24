/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode088
import Proofs.RadenkovicGutmanD4Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .plus e088 e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,96],[0,96,-16]],[[0,0,0],[0,0,0],[0,0]],[[0,0,1152],[0,3888,152],[1152,152]],[[0,0,0],[0,0,0],[0,0]],[[2592,31752,7464],[31752,23616,-152],[7464,-152]],[[0,0,0],[0,0,0],[0,0]],[[254880,302400,19784],[302400,57936,-352],[19784,-352]],[[0,0,0],[0,0,0],[0,0]],[[2963952,1265328,27504],[1265328,73376,-168],[27504,-168]],[[0,0,0],[0,0,0],[0,0]],[[16390896,3070896,21416],[3070896,50144,-24],[21416,-24]],[[0,0,0],[0,0],[0]],[[55272800,4808608,9120],[4808608,16480],[9120]],[[0,0,0],[0,0],[0]],[[126306896,5111872,1752],[5111872,528],[1752]],[[0,0,0],[0,0],[0]],[[206942816,3777584,-48],[3777584,-1312],[-48]],[[0,0,0],[0,0],[0]],[[251304272,1950856,-72],[1950856,-368],[-72]],[[0,0,0],[0,0],[0]],[[230736720,695480,-8],[695480,-32],[-8]],[[0,0],[0]],[[161948784,164904],[164904]],[[0,0],[0]],[[87245488,23776],[23776]],[[0,0],[0]],[[35990288,1576],[1576]],[[0,0],[0]],[[11261824,-32],[-32]],[[0,0],[0]],[[2623792,-8],[-8]],[[0]],[[440576]],[[0]],[[50352]],[[0]],[[3504]],[[0]],[[112]],[[0]],[[0]]]
theorem step091 : p091=NestedHorner.add p088 p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_plus e091 e088 e090 p088 p090 p091 rfl h088 h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
