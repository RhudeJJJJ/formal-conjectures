/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode093
import Proofs.RadenkovicGutmanD19Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,361]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-3249],[0,-6498,10602],[-3249,10602,38]],[[0,0,0],[0,0,0],[0,0]],[[-29241,-109269,38019],[-109269,201894,35796],[38019,35796]],[[0,0,0],[0,0,0],[0,0]],[[-1365606,239571,321917],[239571,1422682,39596],[321917,39596]],[[0,0,0],[0,0,0],[0,0]],[[-7699617,7367193,916066],[7367193,3803610,17024],[916066,17024]],[[0,0,0],[0,0,0],[0,0]],[[4341804,36678360,1345428],[36678360,5371604,2698],[1345428,2698]],[[0,0,0],[0,0,0],[0,0]],[[190231781,94493669,1145244],[94493669,4440908,76],[1145244,76]],[[0,0,0],[0,0],[0]],[[894261068,152058843,585219],[152058843,2218858],[585219]],[[0,0,0],[0,0],[0]],[[2348393654,164649896,177726],[164649896,662530],[177726]],[[0,0,0],[0,0],[0]],[[4136852634,124169845,30039],[124169845,110770],[30039]],[[0,0,0],[0,0],[0]],[[5240932944,66089771,2337],[66089771,8626],[2337]],[[0,0,0],[0,0],[0]],[[4943082864,24764942,38],[24764942,152],[38]],[[0,0],[0]],[[3534374642,6410315],[6410315]],[[0,0],[0]],[[1931343502,1098447],[1098447]],[[0,0],[0]],[[806808685,114285],[114285]],[[0,0],[0]],[[255807716,5928],[5928]],[[0,0],[0]],[[60573786,76],[76]],[[0]],[[10408998]],[[0]],[[1235247]],[[0]],[[92454]],[[0]],[[3591]],[[0]],[[38]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
