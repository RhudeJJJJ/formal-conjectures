/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode043
import Proofs.RadenkovicGutmanD17Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-867],[0,-867,510]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-7803,-13005],[-7803,-42840,8381],[-13005,8381,60]],[[0,0,0],[0,0,0],[0,0]],[[-192780,-530604,-31773],[-530604,-56856,33754],[-31773,33754]],[[0,0,0],[0,0,0],[0,0]],[[-6421140,-3732354,107506],[-3732354,619516,39073],[107506,39073]],[[0,0,0],[0,0,0],[0,0]],[[-60042654,-10625716,552835],[-10625716,2403960,17413],[552835,17413]],[[0,0,0],[0,0,0],[0,0]],[[-286734324,-12202870,976286],[-12202870,3883536,2966],[976286,2966]],[[0,0,0],[0,0,0],[0,0]],[[-839447776,6995382,914265],[6995382,3452076,120],[914265,120]],[[0,0,0],[0,0],[0]],[[-1626094148,43755340,497710],[43755340,1814460],[497710]],[[0,0,0],[0,0],[0]],[[-2132400276,69561727,159337],[69561727,567712],[159337]],[[0,0,0],[0,0],[0]],[[-1825943842,64305439,28563],[64305439,100768],[28563]],[[0,0,0],[0,0],[0]],[[-812361630,39101063,2456],[39101063,8788],[2456]],[[0,0,0],[0,0],[0]],[[201633446,16182912,60],[16182912,240],[60]],[[0,0],[0]],[[653427776,4553409],[4553409]],[[0,0],[0]],[[573587684,845514],[845514]],[[0,0],[0]],[[313404796,96619],[96619]],[[0,0],[0]],[[119360312,5822],[5822]],[[0,0],[0]],[[32529340,120],[120]],[[0]],[[6298646]],[[0]],[[837918]],[[0]],[[71386]],[[0]],[[3366]],[[0]],[[60]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
