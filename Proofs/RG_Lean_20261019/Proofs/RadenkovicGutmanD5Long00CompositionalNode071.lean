/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode043
import Proofs.RadenkovicGutmanD5Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-75],[0,-75,30]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-675,-1125],[-675,-3960,365],[-1125,365,12]],[[0,0,0],[0,0,0],[0,0]],[[-17820,-49140,-4845],[-49140,-15384,1906],[-4845,1906]],[[0,0,0],[0,0,0],[0,0]],[[-612468,-406386,-2918],[-406386,-1700,2521],[-2918,2521]],[[0,0,0],[0,0,0],[0,0]],[[-6131646,-1504852,18619],[-1504852,81816,1333],[18619,1333]],[[0,0,0],[0,0,0],[0,0]],[[-31820196,-3108982,47414],[-3108982,181488,302],[47414,302]],[[0,0,0],[0,0,0],[0,0]],[[-102991888,-3736458,52305],[-3736458,190476,24],[52305,24]],[[0,0,0],[0,0],[0]],[[-226664708,-2238356,32182],[-2238356,114588],[32182]],[[0,0,0],[0,0],[0]],[[-355009620,302455,11665],[302455,41344],[11665]],[[0,0,0],[0,0],[0]],[[-404821906,1792687,2451],[1792687,8800],[2451]],[[0,0,0],[0,0],[0]],[[-337770654,1659959,272],[1659959,1012],[272]],[[0,0,0],[0,0],[0]],[[-202712506,871080,12],[871080,48],[12]],[[0,0],[0]],[[-81970960,293865],[293865]],[[0,0],[0]],[[-16886620,64770],[64770]],[[0,0],[0]],[[2983564,8995],[8995]],[[0,0],[0]],[[3865592,710],[710]],[[0,0],[0]],[[1598812,24],[24]],[[0]],[[402470]],[[0]],[[66510]],[[0]],[[7066]],[[0]],[[438]],[[0]],[[12]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
