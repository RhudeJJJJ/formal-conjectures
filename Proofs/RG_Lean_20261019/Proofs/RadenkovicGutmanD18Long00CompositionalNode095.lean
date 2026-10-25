/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode093
import Proofs.RadenkovicGutmanD18Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,324]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-2916],[0,-5832,9504],[-2916,9504,36]],[[0,0,0],[0,0,0],[0,0]],[[-26244,-98172,34020],[-98172,180792,32112],[34020,32112]],[[0,0,0],[0,0,0],[0,0]],[[-1227636,210924,288360],[210924,1274616,35568],[288360,35568]],[[0,0,0],[0,0,0],[0,0]],[[-6958548,6580764,821016],[6580764,3409128,15336],[821016,15336]],[[0,0,0],[0,0,0],[0,0]],[[3482676,32806224,1206504],[32806224,4816944,2448],[1206504,2448]],[[0,0,0],[0,0,0],[0,0]],[[168801300,84572532,1027728],[84572532,3985200,72],[1027728,72]],[[0,0,0],[0,0],[0]],[[796876020,136162188,525708],[136162188,1993320],[525708]],[[0,0,0],[0,0],[0]],[[2096027640,147509784,159912],[147509784,596232],[159912]],[[0,0,0],[0,0],[0]],[[3695775984,111305340,27108],[111305340,100008],[27108]],[[0,0,0],[0,0],[0]],[[4685388192,59282676,2124],[59282676,7848],[2124]],[[0,0,0],[0,0],[0]],[[4421742912,22233888,36],[22233888,144],[36]],[[0,0],[0]],[[3163417704,5762340],[5762340]],[[0,0],[0]],[[1729672056,989316],[989316]],[[0,0],[0]],[[723049524,103284],[103284]],[[0,0],[0]],[[229437108,5400],[5400]],[[0,0],[0]],[[54385992,72],[72]],[[0]],[[9359136]],[[0]],[[1113084]],[[0]],[[83628]],[[0]],[[3276]],[[0]],[[36]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
