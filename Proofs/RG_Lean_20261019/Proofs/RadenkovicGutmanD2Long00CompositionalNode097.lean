/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode094
import Proofs.RadenkovicGutmanD2Long00CompositionalNode096
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .plus e094 e096
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,24],[0,24,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,288],[0,1116,116],[288,116]],[[0,0,0],[0,0,0],[0,0]],[[1620,9288,2244],[9288,8628,180],[2244,180]],[[0,0,0],[0,0,0],[0,0]],[[92880,97956,7052],[97956,26836,120],[7052,120]],[[0,0,0],[0,0,0],[0,0]],[[1076220,448596,11808],[448596,44340,36],[11808,36]],[[0,0,0],[0,0,0],[0,0]],[[6125244,1184636,11668],[1184636,43064,4],[11668,4]],[[0,0,0],[0,0],[0]],[[21388280,2016980,7096],[2016980,25608],[7096]],[[0,0,0],[0,0],[0]],[[50666068,2341660,2676],[2341660,9380],[2676]],[[0,0,0],[0,0],[0]],[[86069720,1909328,608],[1909328,2052],[608]],[[0,0,0],[0,0],[0]],[[108425620,1108132,76],[1108132,244],[76]],[[0,0,0],[0,0],[0]],[[103413124,458152,4],[458152,12],[4]],[[0,0],[0]],[[75595896,133320],[133320]],[[0,0],[0]],[[42598096,26524],[26524]],[[0,0],[0]],[[18502932,3408],[3408]],[[0,0],[0]],[[6158240,252],[252]],[[0,0],[0]],[[1550100,8],[8]],[[0]],[[288440]],[[0]],[[38204]],[[0]],[[3376]],[[0]],[[176]],[[0]],[[4]]]
theorem step097 : p097=NestedHorner.add p094 p096 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_plus e097 e094 e096 p094 p096 p097 rfl h094 h096 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
