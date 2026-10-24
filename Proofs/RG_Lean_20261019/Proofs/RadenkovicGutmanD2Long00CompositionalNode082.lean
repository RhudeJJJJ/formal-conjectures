/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode079
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e082 : NestedArithmetic.Expr 3 := .scaled (-1) e079
noncomputable def p082 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,216,0],[216,36,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[3564,3132,0],[3132,312,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[58212,19296,0],[19296,1060,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[422928,66860,0],[66860,1832,0],[0,0]],[[0,0,0],[0,0],[0]],[[1816980,145728,0],[145728,1776],[0]],[[0,0,0],[0,0],[0]],[[5180516,212068,0],[212068,1000],[0]],[[0,0,0],[0,0],[0]],[[10431096,213264,0],[213264,324],[0]],[[0,0,0],[0,0],[0]],[[15404464,150992,0],[150992,56],[0]],[[0,0,0],[0,0],[0]],[[17091756,75720,0],[75720,4],[0]],[[0,0],[0]],[[14464536,26716],[26716]],[[0,0],[0]],[[9415080,6480],[6480]],[[0,0],[0]],[[4725472,1028],[1028]],[[0,0],[0]],[[1822828,96],[96]],[[0,0],[0]],[[535028,4],[4]],[[0]],[[117240]],[[0]],[[18560]],[[0]],[[2004]],[[0]],[[132]],[[0]],[[4]]]
theorem step082 : p082=NestedHorner.scale (-1) p079 := by decide +kernel
#print axioms step082
theorem h082 : NestedArithmetic.compile e082=p082 := StagedExprCompile.compile_scaled (-1) e082 e079 p079 p082 rfl h079 step082
#print axioms h082
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
