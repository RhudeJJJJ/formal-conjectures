/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode093
import Proofs.RadenkovicGutmanD38Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1444]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-12996],[0,-25992,42864],[-12996,42864,76]],[[0,0,0],[0,0,0],[0,0]],[[-116964,-432972,156180],[-432972,823992,143792],[156180,143792]],[[0,0,0],[0,0,0],[0,0]],[[-5382396,1122444,1310240],[1122444,5781016,157168],[1310240,157168]],[[0,0,0],[0,0,0],[0,0]],[[-28869588,30725964,3710776],[30725964,15400488,65816],[3710776,65816]],[[0,0,0],[0,0,0],[0,0]],[[33978156,151240304,5422904],[151240304,21651184,9728],[5422904,9728]],[[0,0,0],[0,0,0],[0,0]],[[838463540,387448532,4586448],[387448532,17785520,152],[4586448,152]],[[0,0,0],[0,0],[0]],[[3806860140,620737068,2322028],[620737068,8800040],[2322028]],[[0,0,0],[0,0],[0]],[[9861748600,669214504,694792],[669214504,2585672],[694792]],[[0,0,0],[0,0],[0]],[[17232424224,502212940,114228],[502212940,419368],[114228]],[[0,0,0],[0,0],[0]],[[21701191392,265696836,8284],[265696836,30248],[8284]],[[0,0,0],[0,0],[0]],[[20362293312,98771728,76],[98771728,304],[76]],[[0,0],[0]],[[14486786664,25278740],[25278740]],[[0,0],[0]],[[7874672056,4255316],[4255316]],[[0,0],[0]],[[3270027604,428564],[428564]],[[0,0],[0]],[[1029331308,20520],[20520]],[[0,0],[0]],[[241468872,152],[152]],[[0]],[[40954576]],[[0]],[[4762844]],[[0]],[[343748]],[[0]],[[12236]],[[0]],[[76]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
