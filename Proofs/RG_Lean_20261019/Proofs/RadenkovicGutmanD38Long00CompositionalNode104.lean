/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode092
import Proofs.RadenkovicGutmanD38Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2736,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-24624,-24624,0],[-24624,-23028,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-642276,-272916,0],[-272916,-74632,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6240132,-1284552,0],[-1284552,-119092,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-32901312,-3391500,0],[-3391500,-100168,0],[0,0]],[[0,0,0],[0,0],[0]],[[-109283668,-5588584,0],[-5588584,-42256],[0]],[[0,0,0],[0,0],[0]],[[-247004028,-6024444,0],[-6024444,-5624],[0]],[[0,0,0],[0,0],[0]],[[-397058808,-4295824,0],[-4295824,1900],[0]],[[0,0,0],[0,0],[0]],[[-465549248,-1967944,0],[-1967944,760],[0]],[[0,0,0],[0,0],[0]],[[-402755692,-509504,0],[-509504,76],[0]],[[0,0],[0]],[[-256638776,-26524],[-26524]],[[0,0],[0]],[[-117991672,28120],[28120]],[[0,0],[0]],[[-36770320,9652],[9652]],[[0,0],[0]],[[-6165804,1368],[1368]],[[0,0],[0]],[[397556,76],[76]],[[0]],[[545832]],[[0]],[[155952]],[[0]],[[24092]],[[0]],[[2052]],[[0]],[[76]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
