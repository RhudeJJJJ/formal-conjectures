/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode043
import Proofs.RadenkovicGutmanD36Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,11664],[0,23328,-14688],[11664,-14688,4624]],[[0,0,0],[0,0,0],[0,0]],[[0,392688,-31104],[392688,-309456,19584],[-31104,19584]],[[0,0,0],[0,0,0],[0,0]],[[2649024,990144,-207360],[990144,-1367808,143616],[-207360,143616]],[[0,0,0],[0,0,0],[0,0]],[[14108688,-4886352,35424],[-4886352,-540880,169184],[35424,169184]],[[0,0,0],[0,0,0],[0,0]],[[-22450608,-24508368,1363680],[-24508368,5175904,69088],[1363680,69088]],[[0,0,0],[0,0,0],[0,0]],[[-404048976,-32674800,2758944],[-32674800,11233152,9248],[2758944,9248]],[[0,0,0],[0,0],[0]],[[-1597197824,22760480,2640016],[22760480,10826112],[2640016]],[[0,0,0],[0,0],[0]],[[-3462930848,135111968,1407520],[135111968,5748016],[1407520]],[[0,0,0],[0,0],[0]],[[-4636780544,213179056,427248],[213179056,1733056],[427248]],[[0,0,0],[0,0],[0]],[[-3651359504,193790960,69088],[193790960,278256],[69088]],[[0,0,0],[0,0],[0]],[[-871144160,114729424,4624],[114729424,18496],[4624]],[[0,0],[0]],[[1670674880,45724560],[45724560]],[[0,0],[0]],[[2500946080,12202592],[12202592]],[[0,0],[0]],[[1902180752,2094224],[2094224]],[[0,0],[0]],[[963951040,209168],[209168]],[[0,0],[0]],[[345933984,9248],[9248]],[[0]],[[88803840]],[[0]],[[16013776]],[[0]],[[1931360]],[[0]],[[140080]],[[0]],[[4624]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
