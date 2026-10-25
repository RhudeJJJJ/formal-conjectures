/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode075
import Proofs.RadenkovicGutmanD38Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1444]],[[0,0],[0,0,0],[0,0]],[[0,0,12996],[0,25992,25992],[12996,25992]],[[0,0,0],[0,0,0],[0,0]],[[-116964,428868,229596],[428868,693120,69312],[229596,69312]],[[0,0,0],[0,0,0],[0,0]],[[1481544,6900876,1006468],[6900876,3260552,63536],[1006468,63536]],[[0,0,0],[0,0,0],[0,0]],[[41756148,39754764,2064920],[39754764,6936976,23104],[2064920,23104]],[[0,0,0],[0,0,0],[0,0]],[[321789624,122373224,2373936],[122373224,8213472,2888],[2373936,2888]],[[0,0,0],[0,0],[0]],[[1338933116,234336652,1640384],[234336652,5839536],[1640384]],[[0,0,0],[0,0],[0]],[[3590217200,300824188,694564],[300824188,2544328],[694564]],[[0,0,0],[0,0],[0]],[[6737256360,269421520,176168],[269421520,664240],[176168]],[[0,0,0],[0,0],[0]],[[9266751592,171736364,24548],[171736364,95304],[24548]],[[0,0,0],[0,0],[0]],[[9605733480,78347108,1444],[78347108,5776],[1444]],[[0,0],[0]],[[7629893840,25379744],[25379744]],[[0,0],[0]],[[4685101320,5696580],[5696580]],[[0,0],[0]],[[2229446472,841852],[841852]],[[0,0],[0]],[[819179756,73644],[73644]],[[0,0],[0]],[[229994544,2888],[2888]],[[0]],[[48388440]],[[0]],[[7378840]],[[0]],[[769652]],[[0]],[[49096]],[[0]],[[1444]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
