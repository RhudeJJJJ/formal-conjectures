/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode112
import Proofs.RadenkovicGutmanD17Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,408],[0,408,968]],[[0,0,0],[0,0,0],[0,0,0]],[[0,3672,14076],[3672,14976,19600],[14076,19600,4]],[[0,0,0],[0,0,0],[0,0]],[[177552,340416,197952],[340416,433704,50480],[197952,50480]],[[0,0,0],[0,0,0],[0,0]],[[5337468,4934664,821536],[4934664,2069888,45912],[821536,45912]],[[0,0,0],[0,0,0],[0,0]],[[61421328,27813952,1646016],[27813952,4483048,16752],[1646016,16752]],[[0,0,0],[0,0,0],[0,0]],[[371258484,85463944,1868200],[85463944,5437616,2136],[1868200,2136]],[[0,0,0],[0,0,0],[0,0]],[[1387939880,164799112,1281328],[164799112,3980864,8],[1281328,8]],[[0,0,0],[0,0],[0]],[[3516976340,214085176,540548],[214085176,1792240],[540548]],[[0,0,0],[0,0],[0]],[[6383835168,194638688,137152],[194638688,484968],[137152]],[[0,0,0],[0,0],[0]],[[8596316256,126216704,19252],[126216704,72528],[19252]],[[0,0,0],[0,0],[0]],[[8782688856,58673192,1168],[58673192,4680],[1168]],[[0,0,0],[0,0],[0]],[[6903606288,19395824,4],[19395824,16],[4]],[[0,0],[0]],[[4206002096,4450744],[4450744]],[[0,0],[0]],[[1989563576,674560],[674560]],[[0,0],[0]],[[727826648,60976],[60976]],[[0,0],[0]],[[203757876,2544],[2544]],[[0,0],[0]],[[42820544,8],[8]],[[0]],[[6538576]],[[0]],[[685848]],[[0]],[[44428]],[[0]],[[1376]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
