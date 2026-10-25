/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode043
import Proofs.RadenkovicGutmanD16Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,768],[0,768,-448]],[[0,0,0],[0,0,0],[0,0]],[[0,6912,6912],[6912,28800,-4736],[6912,-4736]],[[0,0,0],[0,0,0],[0,0]],[[171072,286848,12096],[286848,58368,-17408],[12096,-17408]],[[0,0,0],[0,0,0],[0,0]],[[3970944,1768320,-59904],[1768320,-205696,-17920],[-59904,-17920]],[[0,0,0],[0,0,0],[0,0]],[[32045760,4461952,-241664],[4461952,-908032,-6912],[-241664,-6912]],[[0,0,0],[0,0,0],[0,0]],[[138586752,4151808,-374784],[4151808,-1442304,-896],[-374784,-896]],[[0,0,0],[0,0],[0]],[[374488896,-4537984,-315264],[-4537984,-1229056],[-315264]],[[0,0,0],[0,0],[0]],[[675251456,-18384000,-155136],[-18384000,-610176],[-155136]],[[0,0,0],[0,0],[0]],[[825329536,-26127872,-44544],[-26127872,-176384],[-44544]],[[0,0,0],[0,0],[0]],[[651605632,-22271744,-6912],[-22271744,-27520],[-6912]],[[0,0,0],[0,0],[0]],[[247126528,-12587392,-448],[-12587392,-1792],[-448]],[[0,0],[0]],[[-108715520,-4840320],[-4840320]],[[0,0],[0]],[[-240195584,-1255296],[-1255296]],[[0,0],[0]],[[-192423040,-210432],[-210432]],[[0,0],[0]],[[-98290368,-20608],[-20608]],[[0,0],[0]],[[-35121408,-896],[-896]],[[0]],[[-8940160]],[[0]],[[-1596544]],[[0]],[[-190656]],[[0]],[[-13696]],[[0]],[[-448]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
