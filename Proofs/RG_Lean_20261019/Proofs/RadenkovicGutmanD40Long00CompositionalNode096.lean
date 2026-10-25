/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode043
import Proofs.RadenkovicGutmanD40Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4800],[0,4800,-3040]],[[0,0,0],[0,0,0],[0,0]],[[0,43200,43200],[43200,175680,-33920],[43200,-33920]],[[0,0,0],[0,0,0],[0,0]],[[1049760,1753920,56160],[1753920,249600,-120320],[56160,-120320]],[[0,0,0],[0,0,0],[0,0]],[[24131520,10261440,-478080],[10261440,-1827520,-122560],[-478080,-122560]],[[0,0,0],[0,0,0],[0,0]],[[191207520,22949440,-1743680],[22949440,-6828160,-47040],[-1743680,-47040]],[[0,0,0],[0,0,0],[0,0]],[[806794560,10028160,-2630400],[10028160,-10379520,-6080],[-2630400,-6080]],[[0,0,0],[0,0],[0]],[[2107721760,-59913280,-2183040],[-59913280,-8652160],[-2183040]],[[0,0,0],[0,0],[0]],[[3611523200,-156600000,-1065600],[-156600000,-4236480],[-1065600]],[[0,0,0],[0,0],[0]],[[4028739520,-201650240,-304320],[-201650240,-1212800],[-304320]],[[0,0,0],[0,0],[0]],[[2526796480,-164262080,-47040],[-164262080,-187840],[-47040]],[[0,0,0],[0,0],[0]],[[-54174080,-90380800,-3040],[-90380800,-12160],[-3040]],[[0,0],[0]],[[-1948188800,-34132800],[-34132800]],[[0,0],[0]],[[-2280012800,-8736000],[-8736000]],[[0,0],[0]],[[-1573199680,-1449600],[-1449600]],[[0,0],[0]],[[-750467040,-140800],[-140800]],[[0,0],[0]],[[-257735040,-6080],[-6080]],[[0]],[[-63918400]],[[0]],[[-11204800]],[[0]],[[-1319520]],[[0]],[[-93760]],[[0]],[[-3040]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
