/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,675],[0,675]],[[0,0,0],[0,0,0],[0,0]],[[0,-6075,10125],[-6075,30375,3015],[10125,3015]],[[0,0,0],[0,0,0],[0,0]],[[-91125,201285,78435],[201285,225720,3990],[78435,3990]],[[0,0,0],[0,0,0],[0,0]],[[528525,2464020,242370],[2464020,669015,2055],[242370,2055]],[[0,0,0],[0,0,0],[0,0]],[[15556050,11634885,392085],[11634885,1045140,435],[392085,435]],[[0,0,0],[0,0,0],[0,0]],[[108547155,30790920,365610],[30790920,949200,30],[365610,30]],[[0,0,0],[0,0],[0]],[[412628175,51844005,203355],[51844005,518850],[203355]],[[0,0,0],[0,0],[0]],[[1019520420,58972110,67170],[58972110,170055],[67170]],[[0,0,0],[0,0],[0]],[[1769587680,46705725,12495],[46705725,31800],[12495]],[[0,0,0],[0,0],[0]],[[2250633735,26074155,1125],[26074155,2955],[1125]],[[0,0,0],[0,0],[0]],[[2149621530,10241010,30],[10241010,90],[30]],[[0,0],[0]],[[1563379020,2781690],[2781690]],[[0,0],[0]],[[871119900,502650],[502650]],[[0,0],[0]],[[371694105,55920],[55920]],[[0,0],[0]],[[120560355,3240],[3240]],[[0,0],[0]],[[29264400,60],[60]],[[0]],[[5172300]],[[0]],[[635325]],[[0]],[[49905]],[[0]],[[2115]],[[0]],[[30]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
