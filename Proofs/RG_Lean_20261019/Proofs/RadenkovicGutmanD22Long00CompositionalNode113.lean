/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,484]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-8712,8712],[0,8712]],[[0,0,0],[0,0,0],[0,0]],[[39204,-78408,39204],[-78408,81312,23232],[39204,23232]],[[0,0,0],[0,0,0],[0,0]],[[-26136,-182952,209088],[-182952,579832,21296],[209088,21296]],[[0,0,0],[0,0,0],[0,0]],[[-1450548,1332936,470448],[1332936,1438448,7744],[470448,7744]],[[0,0,0],[0,0,0],[0,0]],[[-3993000,8351904,580800],[8351904,1893408,968],[580800,968]],[[0,0,0],[0,0],[0]],[[8404660,22098472,428824],[22098472,1473296],[428824]],[[0,0,0],[0,0],[0]],[[79745776,35346520,193600],[35346520,695992],[193600]],[[0,0,0],[0,0],[0]],[[249150616,37796528,52272],[37796528,195536],[52272]],[[0,0,0],[0,0],[0]],[[479069976,28126208,7744],[28126208,30008],[7744]],[[0,0,0],[0,0],[0]],[[644777056,14764904,484],[14764904,1936],[484]],[[0,0],[0]],[[639379488,5445000],[5445000]],[[0,0],[0]],[[478420448,1379400],[1379400]],[[0,0],[0]],[[272806600,228448],[228448]],[[0,0],[0]],[[118597908,22264],[22264]],[[0,0],[0]],[[38992976,968],[968]],[[0]],[[9524152]],[[0]],[[1673672]],[[0]],[[199892]],[[0]],[[14520]],[[0]],[[484]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
