/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode091
import Proofs.RadenkovicGutmanD3Long00StagedUNode092
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .plus e091 e092
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,9]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-81],[0,-162,234],[-81,234,6]],[[0,0,0],[0,0,0],[0,0]],[[-729,-2997,675],[-2997,3942,852],[675,852]],[[0,0,0],[0,0,0],[0,0]],[[-39366,-4941,6525],[-4941,29466,1068],[6525,1068]],[[0,0,0],[0,0,0],[0,0]],[[-320193,100089,19746],[100089,82458,576],[19746,576]],[[0,0,0],[0,0,0],[0,0]],[[-996084,613464,30804],[613464,122964,138],[30804,138]],[[0,0,0],[0,0,0],[0,0]],[[-412155,1725957,28188],[1725957,109260,12],[28188,12]],[[0,0,0],[0,0],[0]],[[7015980,2959803,15843],[2959803,60330],[15843]],[[0,0,0],[0,0],[0]],[[27422070,3399144,5502],[3399144,20802],[5502]],[[0,0,0],[0,0],[0]],[[57593754,2727765,1143],[2727765,4338],[1143]],[[0,0,0],[0,0],[0]],[[81632592,1558731,129],[1558731,498],[129]],[[0,0,0],[0,0],[0]],[[84012912,636558,6],[636558,24],[6]],[[0,0],[0]],[[64893234,183915],[183915]],[[0,0],[0]],[[38224206,36591],[36591]],[[0,0],[0]],[[17269389,4749],[4749]],[[0,0],[0]],[[5971908,360],[360]],[[0,0],[0]],[[1565082,12],[12]],[[0]],[[304806]],[[0]],[[42639]],[[0]],[[4038]],[[0]],[[231]],[[0]],[[6]]]
theorem step093 : p093=NestedHorner.add p091 p092 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_plus e093 e091 e092 p091 p092 p093 rfl h091 h092 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
