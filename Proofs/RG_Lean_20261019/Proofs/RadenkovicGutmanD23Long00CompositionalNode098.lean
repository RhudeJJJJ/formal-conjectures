/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1587],[0,1587]],[[0,0,0],[0,0,0],[0,0]],[[0,-14283,23805],[-14283,71415,7015],[23805,7015]],[[0,0,0],[0,0,0],[0,0]],[[-214245,472581,183747],[472581,528264,9062],[183747,9062]],[[0,0,0],[0,0,0],[0,0]],[[1232685,5768676,565202],[5768676,1556295,4439],[565202,4439]],[[0,0,0],[0,0,0],[0,0]],[[36332226,27156629,909029],[27156629,2412516,851],[909029,851]],[[0,0,0],[0,0,0],[0,0]],[[253094691,71628440,841018],[71628440,2168624,46],[841018,46]],[[0,0,0],[0,0],[0]],[[960154159,120150229,462507],[120150229,1168354],[462507]],[[0,0,0],[0,0],[0]],[[2367043252,136072094,150098],[136072094,374647],[150098]],[[0,0,0],[0,0],[0]],[[4098441024,107201229,27071],[107201229,67528],[27071]],[[0,0,0],[0,0],[0]],[[5198435735,59452171,2277],[59452171,5819],[2277]],[[0,0,0],[0,0],[0]],[[4949918090,23148994,46],[23148994,138],[46]],[[0,0],[0]],[[3587237964,6212346],[6212346]],[[0,0],[0]],[[1990423772,1102298],[1102298]],[[0,0],[0]],[[844922825,118864],[118864]],[[0,0],[0]],[[272271907,6440],[6440]],[[0,0],[0]],[[65522400,92],[92]],[[0]],[[11441580]],[[0]],[[1379885]],[[0]],[[105041]],[[0]],[[4163]],[[0]],[[46]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
