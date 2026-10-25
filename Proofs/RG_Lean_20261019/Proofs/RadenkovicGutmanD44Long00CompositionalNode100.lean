/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode043
import Proofs.RadenkovicGutmanD44Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-17424],[0,-34848,11088],[-17424,11088]],[[0,0,0],[0,0,0],[0,0]],[[0,-684288,-51216],[-684288,63888,48048],[-51216,48048]],[[0,0,0],[0,0,0],[0,0]],[[-6343920,-5455296,185504],[-5455296,1479808,59136],[185504,59136]],[[0,0,0],[0,0,0],[0,0]],[[-75960720,-15971472,1042624],[-15971472,4964432,25872],[1042624,25872]],[[0,0,0],[0,0,0],[0,0]],[[-401648544,-15458256,1938288],[-15458256,7779552,3696],[1938288,3696]],[[0,0,0],[0,0],[0]],[[-1234535280,25970384,1866656],[25970384,6793600],[1866656]],[[0,0,0],[0,0],[0]],[[-2423030192,101703008,1022208],[101703008,3478464],[1022208]],[[0,0,0],[0,0],[0]],[[-3085456352,153183712,320320],[153183712,1036112],[320320]],[[0,0,0],[0,0],[0]],[[-2324248608,138888288,53504],[138888288,166144],[53504]],[[0,0,0],[0,0],[0]],[[-416401744,83177248,3696],[83177248,11088],[3696]],[[0,0],[0]],[[1295484608,33724416],[33724416]],[[0,0],[0]],[[1834147040,9177520],[9177520]],[[0,0],[0]],[[1389451360,1607408],[1607408]],[[0,0],[0]],[[709192176,163856],[163856]],[[0,0],[0]],[[257438544,7392],[7392]],[[0]],[[66976800]],[[0]],[[12251360]],[[0]],[[1499344]],[[0]],[[110352]],[[0]],[[3696]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
