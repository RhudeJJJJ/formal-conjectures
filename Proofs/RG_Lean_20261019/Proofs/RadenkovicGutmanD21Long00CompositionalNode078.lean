/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode075
import Proofs.RadenkovicGutmanD21Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,441]],[[0,0],[0,0,0],[0,0]],[[0,0,3969],[0,7938,7938],[3969,7938]],[[0,0,0],[0,0,0],[0,0]],[[-35721,130977,70119],[130977,211680,21168],[70119,21168]],[[0,0,0],[0,0,0],[0,0]],[[452466,2107539,307377],[2107539,995778,19404],[307377,19404]],[[0,0,0],[0,0,0],[0,0]],[[12752397,12141171,630630],[12141171,2118564,7056],[630630,7056]],[[0,0,0],[0,0,0],[0,0]],[[98275086,37372986,725004],[37372986,2508408,882],[725004,882]],[[0,0,0],[0,0],[0]],[[408912399,71566803,500976],[71566803,1783404],[500976]],[[0,0,0],[0,0],[0]],[[1096458300,91872207,212121],[91872207,777042],[212121]],[[0,0,0],[0,0],[0]],[[2057569290,82281780,53802],[82281780,202860],[53802]],[[0,0,0],[0,0],[0]],[[2830081338,52448571,7497],[52448571,29106],[7497]],[[0,0,0],[0,0],[0]],[[2933606970,23927337,441],[23927337,1764],[441]],[[0,0],[0]],[[2330182260,7751016],[7751016]],[[0,0],[0]],[[1430837730,1739745],[1739745]],[[0,0],[0]],[[680876658,257103],[257103]],[[0,0],[0]],[[250178859,22491],[22491]],[[0,0],[0]],[[70240716,882],[882]],[[0]],[[14777910]],[[0]],[[2253510]],[[0]],[[235053]],[[0]],[[14994]],[[0]],[[441]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
