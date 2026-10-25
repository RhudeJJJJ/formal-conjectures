/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode033
import Proofs.RadenkovicGutmanD16Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,256]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,4608],[0,4608]],[[0,0,0],[0,0,0],[0,0]],[[-20736,0,20736],[0,82944,12288],[20736,12288]],[[0,0,0],[0,0,0],[0,0]],[[-359424,373248,110592],[373248,442368,11264],[110592,11264]],[[0,0,0],[0,0,0],[0,0]],[[-1099008,2985984,248832],[2985984,995328,4096],[248832,4096]],[[0,0,0],[0,0,0],[0,0]],[[5222400,10699776,307200],[10699776,1228800,512],[307200,512]],[[0,0,0],[0,0],[0]],[[49772288,22671360,226816],[22671360,907264],[226816]],[[0,0,0],[0,0],[0]],[[183732224,31587840,102400],[31587840,409600],[102400]],[[0,0,0],[0,0],[0]],[[419730944,30449664,27648],[30449664,110592],[27648]],[[0,0,0],[0,0],[0]],[[668419072,20805632,4096],[20805632,16384],[4096]],[[0,0,0],[0,0],[0]],[[781878272,10149888,256],[10149888,1024],[256]],[[0,0],[0]],[[690209792,3509760],[3509760]],[[0,0],[0]],[[466214912,839680],[839680]],[[0,0],[0]],[[242206720,132096],[132096]],[[0,0],[0]],[[96581376,12288],[12288]],[[0,0],[0]],[[29282304,512],[512]],[[0]],[[6624768]],[[0]],[[1082368]],[[0]],[[120576]],[[0]],[[8192]],[[0]],[[256]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
