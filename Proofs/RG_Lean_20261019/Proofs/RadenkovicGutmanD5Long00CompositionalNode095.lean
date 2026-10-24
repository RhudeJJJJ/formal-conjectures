/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode093
import Proofs.RadenkovicGutmanD5Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,25]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-225],[0,-450,690],[-225,690,10]],[[0,0,0],[0,0,0],[0,0]],[[-2025,-7965,2235],[-7965,12390,2420],[2235,2420]],[[0,0,0],[0,0,0],[0,0]],[[-102330,675,20105],[675,89770,2860],[20105,2860]],[[0,0,0],[0,0,0],[0,0]],[[-720225,388305,58930],[388305,245370,1400],[58930,1400]],[[0,0,0],[0,0,0],[0,0]],[[-1309800,2101160,89180],[2101160,356020,290],[89180,290]],[[0,0,0],[0,0,0],[0,0]],[[5656565,5625365,78780],[5625365,305420,20],[78780,20]],[[0,0,0],[0,0],[0]],[[39648120,9318315,42355],[9318315,160970],[42355]],[[0,0,0],[0,0],[0]],[[117240310,10373200,13870],[10373200,52130],[13870]],[[0,0,0],[0,0],[0]],[[220071570,8062525,2655],[8062525,9970],[2655]],[[0,0,0],[0,0],[0]],[[291446640,4447155,265],[4447155,1010],[265]],[[0,0,0],[0,0],[0]],[[285120240,1742950,10],[1742950,40],[10]],[[0,0],[0]],[[210898290,479075],[479075]],[[0,0],[0]],[[119274670,89495],[89495]],[[0,0],[0]],[[51724285,10685],[10685]],[[0,0],[0]],[[17123760,720],[720]],[[0,0],[0]],[[4274970,20],[20]],[[0]],[[786910]],[[0]],[[102815]],[[0]],[[8930]],[[0]],[[455]],[[0]],[[10]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
