/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode110
import Proofs.RadenkovicGutmanD2Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e110 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,48],[0,48,8]],[[0,0,0],[0,0,0],[0,0,0]],[[0,432,576],[432,2016,400],[576,400,4]],[[0,0,0],[0,0,0],[0,0]],[[12312,22896,5352],[22896,18984,920],[5352,920]],[[0,0,0],[0,0,0],[0,0]],[[325188,232344,19396],[232344,69728,912],[19396,912]],[[0,0,0],[0,0,0],[0,0]],[[3230928,1105432,37296],[1105432,136648,432],[37296,432]],[[0,0,0],[0,0,0],[0,0]],[[17617164,3103384,42880],[3103384,160976,96],[42880,96]],[[0,0,0],[0,0,0],[0,0]],[[61439360,5702752,31168],[5702752,120224,8],[31168,8]],[[0,0,0],[0,0],[0]],[[148598420,7253416,14648],[7253416,58000],[14648]],[[0,0,0],[0,0],[0]],[[261652608,6592328,4432],[6592328,17928],[4432]],[[0,0,0],[0,0],[0]],[[345999096,4355504,832],[4355504,3408],[832]],[[0,0,0],[0,0],[0]],[[350673576,2105312,88],[2105312,360],[88]],[[0,0,0],[0,0],[0]],[[275971488,741944,4],[741944,16],[4]],[[0,0],[0]],[[169897376,187864],[187864]],[[0,0],[0]],[[82038656,33160],[33160]],[[0,0],[0]],[[31008848,3856],[3856]],[[0,0],[0]],[[9109236,264],[264]],[[0,0],[0]],[[2051744,8],[8]],[[0]],[[346456]],[[0]],[[42288]],[[0]],[[3508]],[[0]],[[176]],[[0]],[[4]]]
theorem step115 : p115=NestedHorner.add p110 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e110 e114 p110 p114 p115 rfl h110 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
