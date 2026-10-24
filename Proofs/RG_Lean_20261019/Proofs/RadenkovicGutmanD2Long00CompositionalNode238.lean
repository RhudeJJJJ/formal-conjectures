/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode237
import Proofs.RadenkovicGutmanD2Long00CompositionalNode001
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e238 : NestedArithmetic.Expr 3 := .times e237 e001
noncomputable def p238 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,0],[0,0],[0,0]],[[4,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[132,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[2004,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[18560,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[117240,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[535028,4,0],[4,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1822828,96,0],[96,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[4725472,1028,0],[1028,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[9415080,6480,0],[6480,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[14464536,26716,0],[26716,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[17091756,75720,0],[75720,4,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[15404464,150992,0],[150992,56,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[10431096,213264,0],[213264,324,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[5180516,212068,0],[212068,1000,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[1816980,145728,0],[145728,1776,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[422928,66860,0],[66860,1832,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[58212,19296,0],[19296,1060,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[3564,3132,0],[3132,312,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,216,0],[216,36,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0],[0,0,0],[0,0]]]
theorem step238 : p238=NestedArithmetic.mul p237 p001 := by decide +kernel
#print axioms step238
theorem h238 : NestedArithmetic.compile e238=p238 := StagedExprCompile.compile_times e238 e237 e001 p237 p001 p238 rfl h237 h001 step238
#print axioms h238
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
