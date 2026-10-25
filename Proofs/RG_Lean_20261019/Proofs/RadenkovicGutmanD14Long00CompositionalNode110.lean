/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode043
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e110 : NestedArithmetic.Expr 3 := .pow e043 2
noncomputable def p110 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,1764],[0,3528,-2016],[1764,-2016,576]],[[0,0,0],[0,0,0],[0,0]],[[0,87696,-2856],[87696,-55824,1632],[-2856,1632]],[[0,0,0],[0,0,0],[0,0]],[[1089936,419904,-28412],[419904,-337336,16896],[-28412,16896]],[[0,0,0],[0,0,0],[0,0]],[[12202272,-63216,-12184],[-63216,-635312,20640],[-12184,20640]],[[0,0,0],[0,0,0],[0,0]],[[60728400,-4825504,138192],[-4825504,-324768,8544],[138192,8544]],[[0,0,0],[0,0,0],[0,0]],[[174914976,-14939504,312808],[-14939504,471248,1152],[312808,1152]],[[0,0,0],[0,0],[0]],[[315097504,-22476128,311844],[-22476128,831624],[311844]],[[0,0,0],[0,0],[0]],[[347354336,-17919392,169976],[-17919392,550000],[169976]],[[0,0,0],[0,0],[0]],[[178947568,-4632768,52324],[-4632768,187400],[52324]],[[0,0,0],[0,0],[0]],[[-84467424,5150192,8544],[5150192,32640],[8544]],[[0,0,0],[0,0],[0]],[[-230387360,6384896,576],[6384896,2304],[576]],[[0,0],[0]],[[-185196640,3478160],[3478160]],[[0,0],[0]],[[-61091216,1119328],[1119328]],[[0,0],[0]],[[18098400,218736],[218736]],[[0,0],[0]],[[31400992,24096],[24096]],[[0,0],[0]],[[17741216,1152],[1152]],[[0]],[[6015760]],[[0]],[[1327200]],[[0]],[[187728]],[[0]],[[15552]],[[0]],[[576]]]
theorem step110 : p110=NestedArithmetic.power p043 2 := by decide +kernel
#print axioms step110
theorem h110 : NestedArithmetic.compile e110=p110 := StagedExprCompile.compile_pow 2 e110 e043 p043 p110 rfl h043 step110
#print axioms h110
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
