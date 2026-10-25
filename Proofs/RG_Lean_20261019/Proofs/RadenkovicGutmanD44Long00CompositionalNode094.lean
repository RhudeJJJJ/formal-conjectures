/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode035
import Proofs.RadenkovicGutmanD44Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-17424],[0,-34848,11088],[-17424,11088]],[[0,0,0],[0,0,0],[0,0]],[[0,-475200,-51216],[-475200,97152,48048],[-51216,48048]],[[0,0,0],[0,0,0],[0,0]],[[-2908224,-2437776,185504],[-2437776,1768096,59136],[185504,59136]],[[0,0,0],[0,0,0],[0,0]],[[-19986912,2545488,1042624],[2545488,5943872,25872],[1042624,25872]],[[0,0,0],[0,0,0],[0,0]],[[4039200,48478144,1938288],[48478144,9472320,3696],[1938288,3696]],[[0,0,0],[0,0],[0]],[[504326592,164875568,1866656],[164875568,8434624],[1866656]],[[0,0,0],[0,0],[0]],[[2523446112,303209456,1022208],[303209456,4402464],[1022208]],[[0,0,0],[0,0],[0]],[[6851776448,355191584,320320],[355191584,1335488],[320320]],[[0,0,0],[0,0],[0]],[[12317379360,281453568,53504],[281453568,217888],[53504]],[[0,0,0],[0,0],[0]],[[15791416256,154436128,3696],[154436128,14784],[3696]],[[0,0],[0]],[[14979730656,58781008],[58781008]],[[0,0],[0]],[[10720007936,15233680],[15233680]],[[0,0],[0]],[[5838413152,2564672],[2564672]],[[0,0],[0]],[[2421077824,252912],[252912]],[[0,0],[0]],[[758623008,11088],[11088]],[[0]],[[176514624]],[[0]],[[29545824]],[[0]],[[3361600]],[[0]],[[232672]],[[0]],[[7392]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
