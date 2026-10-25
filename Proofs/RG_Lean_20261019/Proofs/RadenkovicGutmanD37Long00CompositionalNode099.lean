/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode096
import Proofs.RadenkovicGutmanD37Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,8214],[0,8214,-2590]],[[0,0,0],[0,0,0],[0,0]],[[0,0,98568],[0,335331,-10804],[98568,-10804]],[[0,0,0],[0,0,0],[0,0]],[[344655,2724273,523254],[2724273,1581528,-79550],[523254,-79550]],[[0,0,0],[0,0,0],[0,0]],[[23851125,23700276,1049912],[23700276,2458391,-93610],[1049912,-93610]],[[0,0,0],[0,0,0],[0,0]],[[257602140,89779131,847818],[89779131,372220,-38184],[847818,-38184]],[[0,0,0],[0,0,0],[0,0]],[[1344166599,193280526,-94942],[193280526,-3321416,-5106],[-94942,-5106]],[[0,0,0],[0,0],[0]],[[4280648215,257936805,-689754],[257936805,-4429122],[-689754]],[[0,0,0],[0,0],[0]],[[9188930168,215345920,-533244],[215345920,-2681945],[-533244]],[[0,0,0],[0,0],[0]],[[13991759420,101872618,-193362],[101872618,-871128],[-193362]],[[0,0,0],[0,0],[0]],[[15515672685,11070252,-34854],[11070252,-147001],[-34854]],[[0,0,0],[0,0],[0]],[[12646395464,-18588393,-2516],[-18588393,-10138],[-2516]],[[0,0],[0]],[[7512801826,-13550140],[-13550140]],[[0,0],[0]],[[3130310556,-4726861],[-4726861]],[[0,0],[0]],[[804454777,-949642],[-949642]],[[0,0],[0]],[[48267055,-105413],[-105413]],[[0,0],[0]],[[-55215840,-5032],[-5032]],[[0]],[[-26028760]],[[0]],[[-6168381]],[[0]],[[-873829]],[[0]],[[-70559]],[[0]],[[-2516]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
