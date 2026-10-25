/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode043
import Proofs.RadenkovicGutmanD45Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,18225],[0,36450,-23220],[18225,-23220,7396]],[[0,0,0],[0,0,0],[0,0]],[[0,611145,-51030],[611145,-491382,32508],[-51030,32508]],[[0,0,0],[0,0,0],[0,0]],[[4098276,1466667,-327159],[1466667,-2133690,231168],[-327159,231168]],[[0,0,0],[0,0,0],[0,0]],[[21167352,-8005581,82242],[-8005581,-682702,271244],[82242,271244]],[[0,0,0],[0,0,0],[0,0]],[[-41095998,-38582856,2228832],[-38582856,8574484,110596],[2228832,110596]],[[0,0,0],[0,0,0],[0,0]],[[-651172794,-48857709,4458810],[-48857709,18235548,14792],[4458810,14792]],[[0,0,0],[0,0],[0]],[[-2526912674,43759847,4247821],[43759847,17458734],[4247821]],[[0,0,0],[0,0],[0]],[[-5409345080,225586700,2259190],[225586700,9237802],[2259190]],[[0,0,0],[0,0],[0]],[[-7126552298,349030951,684693],[349030951,2779270],[684693]],[[0,0,0],[0,0],[0]],[[-5416555352,314643617,110596],[314643617,445566],[110596]],[[0,0,0],[0,0],[0]],[[-952316708,185377120,7396],[185377120,29584],[7396]],[[0,0],[0]],[[3011411270,73641345],[73641345]],[[0,0],[0]],[[4196157370,19606325],[19606325]],[[0,0],[0]],[[3127909382,3358715],[3358715]],[[0,0],[0]],[[1569765646,334970],[334970]],[[0,0],[0]],[[560069796,14792],[14792]],[[0]],[[143210010]],[[0]],[[25751020]],[[0]],[[3098948]],[[0]],[[224374]],[[0]],[[7396]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
