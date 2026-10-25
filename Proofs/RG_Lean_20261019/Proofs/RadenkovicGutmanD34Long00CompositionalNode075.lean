/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode033
import Proofs.RadenkovicGutmanD34Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1156]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,20808],[0,20808]],[[0,0,0],[0,0,0],[0,0]],[[-93636,0,93636],[0,374544,55488],[93636,55488]],[[0,0,0],[0,0,0],[0,0]],[[-1623024,1685448,499392],[1685448,1997568,50864],[499392,50864]],[[0,0,0],[0,0,0],[0,0]],[[-4962708,13483584,1123632],[13483584,4494528,18496],[1123632,18496]],[[0,0,0],[0,0,0],[0,0]],[[23582400,48316176,1387200],[48316176,5548800,2312],[1387200,2312]],[[0,0,0],[0,0],[0]],[[224752988,102375360,1024216],[102375360,4096864],[1024216]],[[0,0,0],[0,0],[0]],[[829665824,142638840,462400],[142638840,1849600],[462400]],[[0,0,0],[0,0],[0]],[[1895347544,137499264,124848],[137499264,499392],[124848]],[[0,0,0],[0,0],[0]],[[3018329872,93950432,18496],[93950432,73984],[18496]],[[0,0,0],[0,0],[0]],[[3530669072,45833088,1156],[45833088,4624],[1156]],[[0,0],[0]],[[3116728592,15848760],[15848760]],[[0,0],[0]],[[2105251712,3791680],[3791680]],[[0,0],[0]],[[1093714720,596496],[596496]],[[0,0],[0]],[[436125276,55488],[55488]],[[0,0],[0]],[[132227904,2312],[2312]],[[0]],[[29914968]],[[0]],[[4887568]],[[0]],[[544476]],[[0]],[[36992]],[[0]],[[1156]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
