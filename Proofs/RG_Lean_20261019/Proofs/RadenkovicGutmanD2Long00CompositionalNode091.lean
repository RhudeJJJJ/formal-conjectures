/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode032
import Proofs.RadenkovicGutmanD2Long00CompositionalNode062
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .times e032 e062
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,4]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,96],[0,96,4]],[[0,0,0],[0,0,0],[0,0]],[[-324,-216,540],[-216,2088,368],[540,368]],[[0,0,0],[0,0,0],[0,0]],[[-9180,8208,3564],[8208,13632,496],[3564,496]],[[0,0,0],[0,0,0],[0,0]],[[-43308,85896,9792],[85896,37048,296],[9792,296]],[[0,0,0],[0,0,0],[0,0]],[[75660,365032,14744],[365032,55312,80],[14744,80]],[[0,0,0],[0,0,0],[0,0]],[[1387796,895776,13432],[895776,50176,8],[13432,8]],[[0,0,0],[0,0],[0]],[[6160740,1435888,7696],[1435888,28784],[7696]],[[0,0,0],[0,0],[0]],[[16078472,1595048,2784],[1595048,10488],[2784]],[[0,0,0],[0,0],[0]],[[28805064,1265896,616],[1265896,2352],[616]],[[0,0,0],[0,0],[0]],[[37735096,727736,76],[727736,296],[76]],[[0,0,0],[0,0],[0]],[[37339776,303432,4],[303432,16],[4]],[[0,0],[0]],[[28407088,90760],[90760]],[[0,0],[0]],[[16760544,18960],[18960]],[[0,0],[0]],[[7684644,2624],[2624]],[[0,0],[0]],[[2726724,216],[216]],[[0,0],[0]],[[740616,8],[8]],[[0]],[[150952]],[[0]],[[22324]],[[0]],[[2260]],[[0]],[[140]],[[0]],[[4]]]
theorem step091 : p091=NestedArithmetic.mul p032 p062 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_times e091 e032 e062 p032 p062 p091 rfl h032 h062 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
