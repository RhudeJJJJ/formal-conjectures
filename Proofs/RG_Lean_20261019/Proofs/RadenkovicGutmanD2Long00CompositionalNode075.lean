/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .scaled (-1) e074
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,36],[0,72],[36]],[[0,0,0],[0,0],[0]],[[0,1188,312],[1188,624],[312]],[[0,0,0],[0,0],[0]],[[9720,13284,1060],[13284,2120],[1060]],[[0,0,0],[0,0],[0]],[[132840,63468,1832],[63468,3664],[1832]],[[0,0,0],[0,0],[0]],[[809784,171800,1776],[171800,3552],[1776]],[[0,0,0],[0,0],[0]],[[2931264,294892,1000],[294892,2000],[1000]],[[0,0,0],[0,0],[0]],[[7074384,339748,324],[339748,648],[324]],[[0,0,0],[0,0],[0]],[[12104464,270544,56],[270544,112],[56]],[[0,0,0],[0,0],[0]],[[15225624,150636,4],[150636,8],[4]],[[0,0],[0]],[[14391832,58436],[58436]],[[0,0],[0]],[[10350912,15464],[15464]],[[0,0],[0]],[[5693512,2660],[2660]],[[0,0],[0]],[[2391272,268],[268]],[[0,0],[0]],[[760112,12],[12]],[[0]],[[179568]],[[0]],[[30528]],[[0]],[[3528]],[[0]],[[248]],[[0]],[[8]]]
theorem step075 : p075=NestedHorner.scale (-1) p074 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_scaled (-1) e075 e074 p074 p075 rfl h074 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
