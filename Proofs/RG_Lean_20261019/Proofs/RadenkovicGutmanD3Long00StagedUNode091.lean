/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode032
import Proofs.RadenkovicGutmanD3Long00StagedUNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .times e032 e063
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,9]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,216],[0,216,6]],[[0,0,0],[0,0,0],[0,0]],[[-729,-486,1215],[-486,4698,774],[1215,774]],[[0,0,0],[0,0,0],[0,0]],[[-20412,18468,7776],[18468,29700,972],[7776,972]],[[0,0,0],[0,0,0],[0,0]],[[-93231,188892,20736],[188892,78174,534],[20736,534]],[[0,0,0],[0,0,0],[0,0]],[[183114,786330,30258],[786330,112788,132],[30258,132]],[[0,0,0],[0,0,0],[0,0]],[[3061341,1890108,26622],[1890108,98496,12],[26622,12]],[[0,0,0],[0,0],[0]],[[13278396,2965068,14658],[2965068,54132],[14658]],[[0,0,0],[0,0],[0]],[[34023450,3218688,5064],[3218688,18798],[5064]],[[0,0,0],[0,0],[0]],[[59892672,2491434,1062],[2491434,3996],[1062]],[[0,0,0],[0,0],[0]],[[77070930,1393590,123],[1393590,474],[123]],[[0,0,0],[0,0],[0]],[[74851860,563778,6],[563778,24],[6]],[[0,0],[0]],[[55827552,163080],[163080]],[[0,0],[0]],[[32247768,32820],[32820]],[[0,0],[0]],[[14452089,4356],[4356]],[[0,0],[0]],[[5003316,342],[342]],[[0,0],[0]],[[1323234,12],[12]],[[0]],[[262008]],[[0]],[[37545]],[[0]],[[3672]],[[0]],[[219]],[[0]],[[6]]]
theorem step091 : p091=NestedArithmetic.mul p032 p063 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_times e091 e032 e063 p032 p063 p091 rfl h032 h063 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
