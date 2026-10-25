/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode043
import Proofs.RadenkovicGutmanD20Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1200],[0,-1200,720]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-10800,-18000],[-10800,-59040,11960],[-18000,11960,72]],[[0,0,0],[0,0,0],[0,0]],[[-265680,-731160,-41880],[-731160,-68304,47656],[-41880,47656]],[[0,0,0],[0,0,0],[0,0]],[[-8830728,-5083056,160672],[-5083056,910720,54736],[160672,54736]],[[0,0,0],[0,0,0],[0,0]],[[-82178496,-14135152,792544],[-14135152,3443856,24088],[792544,24088]],[[0,0,0],[0,0,0],[0,0]],[[-390008136,-14923552,1384184],[-14923552,5509248,3992],[1384184,3992]],[[0,0,0],[0,0,0],[0,0]],[[-1132537888,13742832,1287120],[13742832,4862016,144],[1287120,144]],[[0,0,0],[0,0],[0]],[[-2168759048,66027664,695992],[66027664,2536608],[695992]],[[0,0,0],[0,0],[0]],[[-2791616640,101258320,220960],[101258320,786064],[220960]],[[0,0,0],[0,0],[0]],[[-2300323216,92097352,39096],[92097352,137440],[39096]],[[0,0,0],[0,0],[0]],[[-884156544,55399304,3272],[55399304,11632],[3272]],[[0,0,0],[0,0],[0]],[[471019664,22720680,72],[22720680,288],[72]],[[0,0],[0]],[[1020505040,6333840],[6333840]],[[0,0],[0]],[[846654560,1162920],[1162920]],[[0,0],[0]],[[451366624,130720],[130720]],[[0,0],[0]],[[169261592,7640],[7640]],[[0,0],[0]],[[45563872,144],[144]],[[0]],[[8718320]],[[0]],[[1144080]],[[0]],[[95656]],[[0]],[[4368]],[[0]],[[72]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
