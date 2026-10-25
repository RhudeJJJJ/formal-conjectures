/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode070
import Proofs.RadenkovicGutmanD15Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,360],[0,360,736]],[[0,0,0],[0,0,0],[0,0,0]],[[0,3240,11340],[3240,27288,15168],[11340,15168,4]],[[0,0,0],[0,0,0],[0,0]],[[-18144,383292,155736],[383292,465852,38880],[155736,38880]],[[0,0,0],[0,0,0],[0,0]],[[2202336,5076432,642096],[5076432,2032208,35336],[642096,35336]],[[0,0,0],[0,0,0],[0,0]],[[36527220,27250140,1282800],[27250140,4197756,12912],[1282800,12912]],[[0,0,0],[0,0,0],[0,0]],[[247790244,80940492,1453848],[80940492,4900024,1656],[1453848,1656]],[[0,0,0],[0,0,0],[0,0]],[[971670940,151768676,996496],[151768676,3460896,8],[996496,8]],[[0,0,0],[0,0],[0]],[[2517176384,192226648,420404],[192226648,1505968],[420404]],[[0,0,0],[0,0],[0]],[[4618692152,170639616,106768],[170639616,394748],[106768]],[[0,0,0],[0,0],[0]],[[6254052896,108151956,15028],[108151956,57376],[15028]],[[0,0,0],[0,0],[0]],[[6409676924,49185108,920],[49185108,3628],[920]],[[0,0,0],[0,0],[0]],[[5048894808,15922900,4],[15922900,16],[4]],[[0,0],[0]],[[3081429360,3582620],[3582620]],[[0,0],[0]],[[1460155512,533320],[533320]],[[0,0],[0]],[[535177044,47500],[47500]],[[0,0],[0]],[[150152080,1972],[1972]],[[0,0],[0]],[[31637064,8],[8]],[[0]],[[4846720]],[[0]],[[510708]],[[0]],[[33336]],[[0]],[[1052]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
