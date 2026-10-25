/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode043
import Proofs.RadenkovicGutmanD19Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1083],[0,-1083,646]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-9747,-16245],[-9747,-53352,10697],[-16245,10697,68]],[[0,0,0],[0,0,0],[0,0]],[[-240084,-660744,-38361],[-660744,-64440,42758],[-38361,42758]],[[0,0,0],[0,0,0],[0,0]],[[-7984980,-4609746,141814],[-4609746,807612,49225],[141814,49225]],[[0,0,0],[0,0,0],[0,0]],[[-74415078,-12910708,707923],[-12910708,3076808,21745],[707923,21745]],[[0,0,0],[0,0,0],[0,0]],[[-353825964,-13996782,1240410],[-13996782,4936224,3634],[1240410,3634]],[[0,0,0],[0,0,0],[0,0]],[[-1029997800,11313038,1155841],[11313038,4365612,136],[1155841,136]],[[0,0,0],[0,0],[0]],[[-1979301524,58124716,626258],[58124716,2282684],[626258]],[[0,0,0],[0,0],[0]],[[-2562328132,90053599,199321],[90053599,709424],[199321]],[[0,0,0],[0,0],[0]],[[-2136903474,82292771,35407],[82292771,124608],[35407]],[[0,0,0],[0,0],[0]],[[-862307254,49658203,2988],[49658203,10644],[2988]],[[0,0,0],[0,0],[0]],[[373744270,20420988,68],[20420988,272],[68]],[[0,0],[0]],[[890002504,5708561],[5708561]],[[0,0],[0]],[[750056788,1051686],[1051686]],[[0,0],[0]],[[402696836,118811],[118811]],[[0,0],[0]],[[151693272,7010],[7010]],[[0,0],[0]],[[40983388,136],[136]],[[0]],[[7869734]],[[0]],[[1036990]],[[0]],[[87202]],[[0]],[[4022]],[[0]],[[68]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
