/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode095
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .scaled (-1) e095
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,27],[0,27]],[[0,0,0],[0,0,0],[0,0]],[[0,-243,405],[-243,1215,135],[405,135]],[[0,0,0],[0,0,0],[0,0]],[[-3645,8181,3267],[8181,9504,222],[3267,222]],[[0,0,0],[0,0,0],[0,0]],[[23085,103356,10602],[103356,30015,159],[10602,159]],[[0,0,0],[0,0,0],[0,0]],[[669546,504189,18189],[504189,50556,51],[18189,51]],[[0,0,0],[0,0,0],[0,0]],[[4755051,1381200,18258],[1381200,50304,6],[18258,6]],[[0,0,0],[0,0],[0]],[[18457839,2414349,11187],[2414349,30834],[11187]],[[0,0,0],[0,0],[0]],[[46643052,2863254,4218],[2863254,11727],[4218]],[[0,0,0],[0,0],[0]],[[82924944,2378709,951],[2378709,2688],[951]],[[0,0,0],[0,0],[0]],[[108231615,1405131,117],[1405131,339],[117]],[[0,0,0],[0,0],[0]],[[106348530,591354,6],[591354,18],[6]],[[0,0],[0]],[[79838604,175386],[175386]],[[0,0],[0]],[[46129212,35658],[35658]],[[0,0],[0]],[[20536065,4704],[4704]],[[0,0],[0]],[[7009587,360],[360]],[[0,0],[0]],[[1812600,12],[12]],[[0]],[[347580]],[[0]],[[47685]],[[0]],[[4401]],[[0]],[[243]],[[0]],[[6]]]
theorem step096 : p096=NestedHorner.scale (-1) p095 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_scaled (-1) e096 e095 p095 p096 rfl h095 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
