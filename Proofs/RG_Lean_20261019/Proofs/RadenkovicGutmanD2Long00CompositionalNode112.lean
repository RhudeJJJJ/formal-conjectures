/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode034
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e112 : NestedArithmetic.Expr 3 := .pow e034 2
noncomputable def p112 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,36],[0,72],[36]],[[0,0,0],[0,0],[0]],[[0,1296,312],[1296,624],[312]],[[0,0,0],[0,0],[0]],[[11664,14688,1060],[14688,2120],[1060]],[[0,0,0],[0,0],[0]],[[163296,71280,1832],[71280,3664],[1832]],[[0,0,0],[0,0],[0]],[[1022544,196320,1776],[196320,3552],[1776]],[[0,0,0],[0,0],[0]],[[3811104,343216,1000],[343216,2000],[1000]],[[0,0,0],[0,0],[0]],[[9487584,402880,324],[402880,648],[324]],[[0,0,0],[0,0],[0]],[[16767072,326816,56],[326816,112],[56]],[[0,0,0],[0,0],[0]],[[21803056,185280,4],[185280,8],[4]],[[0,0],[0]],[[21316512,73136],[73136]],[[0,0],[0]],[[15861152,19680],[19680]],[[0,0],[0]],[[9025952,3440],[3440]],[[0,0],[0]],[[3921328,352],[352]],[[0,0],[0]],[[1289056,16],[16]],[[0]],[[314848]],[[0]],[[55328]],[[0]],[[6608]],[[0]],[[480]],[[0]],[[16]]]
theorem step112 : p112=NestedArithmetic.power p034 2 := by decide +kernel
#print axioms step112
theorem h112 : NestedArithmetic.compile e112=p112 := StagedExprCompile.compile_pow 2 e112 e034 p034 p112 rfl h034 step112
#print axioms h112
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
