/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode043
import Proofs.RadenkovicGutmanD9Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-243],[0,-243,126]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-2187,-3645],[-2187,-12312,1917],[-3645,1917,28]],[[0,0,0],[0,0,0],[0,0]],[[-55404,-152604,-11421],[-152604,-28440,8298],[-11421,8298]],[[0,0,0],[0,0,0],[0,0]],[[-1867860,-1145826,15714],[-1145826,108732,10065],[15714,10065]],[[0,0,0],[0,0,0],[0,0]],[[-17945118,-3671028,121203],[-3671028,529208,4805],[121203,4805]],[[0,0,0],[0,0,0],[0,0]],[[-88670484,-5822262,232110],[-5822262,917584,934],[232110,934]],[[0,0,0],[0,0,0],[0,0]],[[-270983040,-3049482,227721],[-3049482,854892,56],[227721,56]],[[0,0,0],[0,0],[0]],[[-556033604,5431436,129118],[5431436,469884],[129118]],[[0,0,0],[0,0],[0]],[[-794677652,13161839,43321],[13161839,155104],[43321]],[[0,0,0],[0,0],[0]],[[-793836674,13980511,8307],[13980511,29728],[8307]],[[0,0,0],[0,0],[0]],[[-529285214,9206663,808],[9206663,2964],[808]],[[0,0,0],[0,0],[0]],[[-187610330,4048048,28],[4048048,112],[28]],[[0,0],[0]],[[32866784,1204881],[1204881]],[[0,0],[0]],[[90730468,238106],[238106]],[[0,0],[0]],[[63537116,29531],[29531]],[[0,0],[0]],[[27410872,2030],[2030]],[[0,0],[0]],[[8138748,56],[56]],[[0]],[[1695414]],[[0]],[[243070]],[[0]],[[22682]],[[0]],[[1222]],[[0]],[[28]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
