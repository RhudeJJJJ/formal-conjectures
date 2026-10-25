/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,867],[0,867]],[[0,0,0],[0,0,0],[0,0]],[[0,7803,13005],[7803,41616,3859],[13005,3859]],[[0,0,0],[0,0,0],[0,0]],[[140454,484704,100623],[484704,312324,5066],[100623,5066]],[[0,0,0],[0,0,0],[0,0]],[[4885596,4557258,310454],[4557258,935476,2567],[310454,2567]],[[0,0,0],[0,0,0],[0,0]],[[50565276,19769572,501245],[19769572,1475532,527],[501245,527]],[[0,0,0],[0,0,0],[0,0]],[[271025424,50088290,466174],[50088290,1351432,34],[466174,34]],[[0,0,0],[0,0],[0]],[[906304782,82008170,258315],[82008170,744260],[258315]],[[0,0,0],[0,0],[0]],[[2070814676,91407708,84830],[91407708,245684],[84830]],[[0,0,0],[0,0],[0]],[[3405364928,71274081,15623],[71274081,46308],[15623]],[[0,0,0],[0,0],[0]],[[4160637018,39314013,1377],[39314013,4352],[1377]],[[0,0,0],[0,0],[0]],[[3852002426,15306341,34],[15306341,136],[34]],[[0,0],[0]],[[2733291586,4135964],[4135964]],[[0,0],[0]],[[1493696160,747031],[747031]],[[0,0],[0]],[[627971092,83742],[83742]],[[0,0],[0]],[[201606842,4981],[4981]],[[0,0],[0]],[[48683240,102],[102]],[[0]],[[8614784]],[[0]],[[1069538]],[[0]],[[86360]],[[0]],[[3910]],[[0]],[[68]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
