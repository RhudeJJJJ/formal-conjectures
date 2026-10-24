/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode217
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .scaled (-1) e217
noncomputable def p218 : NestedHorner.Poly 3 := [[[8],[0],[0]],[[0,0],[0,0],[0]],[[248,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[3528,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[30528,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[179568,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[760112,12,0],[12,0],[0]],[[0,0,0],[0,0],[0]],[[2391272,268,0],[268,0],[0]],[[0,0,0],[0,0],[0]],[[5693512,2660,0],[2660,0],[0]],[[0,0,0],[0,0],[0]],[[10350912,15464,0],[15464,0],[0]],[[0,0,0],[0,0],[0]],[[14391832,58436,0],[58436,0],[0]],[[0,0,0],[0,0],[0]],[[15225624,150636,4],[150636,8],[4]],[[0,0,0],[0,0],[0]],[[12104464,270544,56],[270544,112],[56]],[[0,0,0],[0,0],[0]],[[7074384,339748,324],[339748,648],[324]],[[0,0,0],[0,0],[0]],[[2931264,294892,1000],[294892,2000],[1000]],[[0,0,0],[0,0],[0]],[[809784,171800,1776],[171800,3552],[1776]],[[0,0,0],[0,0],[0]],[[132840,63468,1832],[63468,3664],[1832]],[[0,0,0],[0,0],[0]],[[9720,13284,1060],[13284,2120],[1060]],[[0,0,0],[0,0],[0]],[[0,1188,312],[1188,624],[312]],[[0,0,0],[0,0],[0]],[[0,0,36],[0,72],[36]]]
theorem step218 : p218=NestedHorner.scale (-1) p217 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_scaled (-1) e218 e217 p217 p218 rfl h217 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
