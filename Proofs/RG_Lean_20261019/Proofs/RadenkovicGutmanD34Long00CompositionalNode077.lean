/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,10404],[0,20808],[10404]],[[0,0,0],[0,0],[0]],[[0,343332,90168],[343332,180336],[90168]],[[0,0,0],[0,0],[0]],[[2809080,3839076,306340],[3839076,612680],[306340]],[[0,0,0],[0,0],[0]],[[38390760,18342252,529448],[18342252,1058896],[529448]],[[0,0,0],[0,0],[0]],[[234027576,49650200,513264],[49650200,1026528],[513264]],[[0,0,0],[0,0],[0]],[[847135296,85223788,289000],[85223788,578000],[289000]],[[0,0,0],[0,0],[0]],[[2044496976,98187172,93636],[98187172,187272],[93636]],[[0,0,0],[0,0],[0]],[[3498190096,78187216,16184],[78187216,32368],[16184]],[[0,0,0],[0,0],[0]],[[4400205336,43533804,1156],[43533804,2312],[1156]],[[0,0],[0]],[[4159239448,16888004],[16888004]],[[0,0],[0]],[[2991413568,4469096],[4469096]],[[0,0],[0]],[[1645424968,768740],[768740]],[[0,0],[0]],[[691077608,77452],[77452]],[[0,0],[0]],[[219672368,3468],[3468]],[[0]],[[51895152]],[[0]],[[8822592]],[[0]],[[1019592]],[[0]],[[71672]],[[0]],[[2312]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
